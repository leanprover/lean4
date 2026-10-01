// Lean compiler output
// Module: Lean.Meta.Sym.Util
// Imports: public import Lean.Meta.Sym.SymM public import Lean.Meta.Transform import Lean.Util.ForEachExpr public import Lean.Meta.Sym.AlphaShareBuilder
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
extern lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_checkMaxShared___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_checkMaxShared___closed__0;
static lean_once_cell_t l_Lean_Expr_checkMaxShared___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_checkMaxShared___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___redArg___lam__0(lean_object* v_k_1_, lean_object* v_____do__lift_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_k_1_, v_____do__lift_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___redArg___lam__1(lean_object* v___x_4_, lean_object* v_inst_5_, lean_object* v_toBind_6_, lean_object* v___f_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_9_ = l_Lean_Expr_fvarId_x21(v_x_8_);
v___x_10_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v___x_4_, v___x_9_);
v___x_11_ = lean_apply_2(v_inst_5_, lean_box(0), v___x_10_);
v___x_12_ = lean_apply_4(v_toBind_6_, lean_box(0), lean_box(0), v___x_11_, v___f_7_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___redArg___lam__1___boxed(lean_object* v___x_13_, lean_object* v_inst_14_, lean_object* v_toBind_15_, lean_object* v___f_16_, lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_Sym_withLocalDeclS___redArg___lam__1(v___x_13_, v_inst_14_, v_toBind_15_, v___f_16_, v_x_17_);
lean_dec_ref(v_x_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___redArg(lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_name_22_, uint8_t v_bi_23_, lean_object* v_type_24_, lean_object* v_k_25_){
_start:
{
lean_object* v___x_26_; lean_object* v_toBind_27_; lean_object* v___f_28_; lean_object* v___f_29_; uint8_t v___x_30_; lean_object* v___x_31_; 
v___x_26_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM;
v_toBind_27_ = lean_ctor_get(v_inst_19_, 1);
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withLocalDeclS___redArg___lam__0), 2, 1);
lean_closure_set(v___f_28_, 0, v_k_25_);
lean_inc(v_toBind_27_);
v___f_29_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withLocalDeclS___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_29_, 0, v___x_26_);
lean_closure_set(v___f_29_, 1, v_inst_21_);
lean_closure_set(v___f_29_, 2, v_toBind_27_);
lean_closure_set(v___f_29_, 3, v___f_28_);
v___x_30_ = 0;
v___x_31_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_20_, v_inst_19_, v_name_22_, v_bi_23_, v_type_24_, v___f_29_, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___redArg___boxed(lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_name_35_, lean_object* v_bi_36_, lean_object* v_type_37_, lean_object* v_k_38_){
_start:
{
uint8_t v_bi_boxed_39_; lean_object* v_res_40_; 
v_bi_boxed_39_ = lean_unbox(v_bi_36_);
v_res_40_ = l_Lean_Meta_Sym_withLocalDeclS___redArg(v_inst_32_, v_inst_33_, v_inst_34_, v_name_35_, v_bi_boxed_39_, v_type_37_, v_k_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS(lean_object* v_n_41_, lean_object* v_00_u03b1_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_name_46_, uint8_t v_bi_47_, lean_object* v_type_48_, lean_object* v_k_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Meta_Sym_withLocalDeclS___redArg(v_inst_43_, v_inst_44_, v_inst_45_, v_name_46_, v_bi_47_, v_type_48_, v_k_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___boxed(lean_object* v_n_51_, lean_object* v_00_u03b1_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_name_56_, lean_object* v_bi_57_, lean_object* v_type_58_, lean_object* v_k_59_){
_start:
{
uint8_t v_bi_boxed_60_; lean_object* v_res_61_; 
v_bi_boxed_60_ = lean_unbox(v_bi_57_);
v_res_61_ = l_Lean_Meta_Sym_withLocalDeclS(v_n_51_, v_00_u03b1_52_, v_inst_53_, v_inst_54_, v_inst_55_, v_name_56_, v_bi_boxed_60_, v_type_58_, v_k_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___redArg(lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_name_65_, lean_object* v_type_66_, lean_object* v_val_67_, lean_object* v_k_68_, uint8_t v_nondep_69_){
_start:
{
lean_object* v___x_70_; lean_object* v_toBind_71_; lean_object* v___f_72_; lean_object* v___f_73_; uint8_t v___x_74_; lean_object* v___x_75_; 
v___x_70_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM;
v_toBind_71_ = lean_ctor_get(v_inst_62_, 1);
v___f_72_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withLocalDeclS___redArg___lam__0), 2, 1);
lean_closure_set(v___f_72_, 0, v_k_68_);
lean_inc(v_toBind_71_);
v___f_73_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withLocalDeclS___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_73_, 0, v___x_70_);
lean_closure_set(v___f_73_, 1, v_inst_64_);
lean_closure_set(v___f_73_, 2, v_toBind_71_);
lean_closure_set(v___f_73_, 3, v___f_72_);
v___x_74_ = 0;
v___x_75_ = l_Lean_Meta_withLetDecl___redArg(v_inst_63_, v_inst_62_, v_name_65_, v_type_66_, v_val_67_, v___f_73_, v_nondep_69_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___redArg___boxed(lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_name_79_, lean_object* v_type_80_, lean_object* v_val_81_, lean_object* v_k_82_, lean_object* v_nondep_83_){
_start:
{
uint8_t v_nondep_boxed_84_; lean_object* v_res_85_; 
v_nondep_boxed_84_ = lean_unbox(v_nondep_83_);
v_res_85_ = l_Lean_Meta_Sym_withLetDeclS___redArg(v_inst_76_, v_inst_77_, v_inst_78_, v_name_79_, v_type_80_, v_val_81_, v_k_82_, v_nondep_boxed_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS(lean_object* v_n_86_, lean_object* v_00_u03b1_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_name_91_, lean_object* v_type_92_, lean_object* v_val_93_, lean_object* v_k_94_, uint8_t v_nondep_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Meta_Sym_withLetDeclS___redArg(v_inst_88_, v_inst_89_, v_inst_90_, v_name_91_, v_type_92_, v_val_93_, v_k_94_, v_nondep_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___boxed(lean_object* v_n_97_, lean_object* v_00_u03b1_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_name_102_, lean_object* v_type_103_, lean_object* v_val_104_, lean_object* v_k_105_, lean_object* v_nondep_106_){
_start:
{
uint8_t v_nondep_boxed_107_; lean_object* v_res_108_; 
v_nondep_boxed_107_ = lean_unbox(v_nondep_106_);
v_res_108_ = l_Lean_Meta_Sym_withLetDeclS(v_n_97_, v_00_u03b1_98_, v_inst_99_, v_inst_100_, v_inst_101_, v_name_102_, v_type_103_, v_val_104_, v_k_105_, v_nondep_boxed_107_);
return v_res_108_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0(void){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0(lean_object* v_msg_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_452__overap_119_; lean_object* v___x_120_; 
v___x_118_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0);
v___x_452__overap_119_ = lean_panic_fn_borrowed(v___x_118_, v_msg_110_);
lean_inc(v___y_116_);
lean_inc_ref(v___y_115_);
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
v___x_120_ = lean_apply_7(v___x_452__overap_119_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, lean_box(0));
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___boxed(lean_object* v_msg_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0(v_msg_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(lean_object* v_e_130_, lean_object* v___y_131_){
_start:
{
uint8_t v___x_133_; 
v___x_133_ = l_Lean_Expr_hasMVar(v_e_130_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v_e_130_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v_mctx_136_; lean_object* v___x_137_; lean_object* v_fst_138_; lean_object* v_snd_139_; lean_object* v___x_140_; lean_object* v_cache_141_; lean_object* v_zetaDeltaFVarIds_142_; lean_object* v_postponed_143_; lean_object* v_diag_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_153_; 
v___x_135_ = lean_st_ref_get(v___y_131_);
v_mctx_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc_ref(v_mctx_136_);
lean_dec(v___x_135_);
v___x_137_ = l_Lean_instantiateMVarsCore(v_mctx_136_, v_e_130_);
v_fst_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_fst_138_);
v_snd_139_ = lean_ctor_get(v___x_137_, 1);
lean_inc(v_snd_139_);
lean_dec_ref(v___x_137_);
v___x_140_ = lean_st_ref_take(v___y_131_);
v_cache_141_ = lean_ctor_get(v___x_140_, 1);
v_zetaDeltaFVarIds_142_ = lean_ctor_get(v___x_140_, 2);
v_postponed_143_ = lean_ctor_get(v___x_140_, 3);
v_diag_144_ = lean_ctor_get(v___x_140_, 4);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; 
v_unused_154_ = lean_ctor_get(v___x_140_, 0);
lean_dec(v_unused_154_);
v___x_146_ = v___x_140_;
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_diag_144_);
lean_inc(v_postponed_143_);
lean_inc(v_zetaDeltaFVarIds_142_);
lean_inc(v_cache_141_);
lean_dec(v___x_140_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v_snd_139_);
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_snd_139_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_cache_141_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_zetaDeltaFVarIds_142_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v_postponed_143_);
lean_ctor_set(v_reuseFailAlloc_152_, 4, v_diag_144_);
v___x_149_ = v_reuseFailAlloc_152_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_st_ref_put(v___y_131_, v___x_149_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v_fst_138_);
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg___boxed(lean_object* v_e_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(v_e_155_, v___y_156_);
lean_dec(v___y_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1(lean_object* v_e_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(v_e_159_, v___y_163_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___boxed(lean_object* v_e_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1(v_e_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
return v_res_176_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_preprocessExpr___closed__3(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_180_ = ((lean_object*)(l_Lean_Meta_Sym_preprocessExpr___closed__2));
v___x_181_ = lean_unsigned_to_nat(2u);
v___x_182_ = lean_unsigned_to_nat(36u);
v___x_183_ = ((lean_object*)(l_Lean_Meta_Sym_preprocessExpr___closed__1));
v___x_184_ = ((lean_object*)(l_Lean_Meta_Sym_preprocessExpr___closed__0));
v___x_185_ = l_mkPanicMessageWithDecl(v___x_184_, v___x_183_, v___x_182_, v___x_181_, v___x_180_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessExpr(lean_object* v_e_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_187_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; uint8_t v_enforceUnfoldReducible_196_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_194_, 1);
v_enforceUnfoldReducible_196_ = lean_ctor_get_uint8(v_a_195_, 1);
lean_dec(v_a_195_);
if (v_enforceUnfoldReducible_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec_ref(v_e_186_);
v___x_197_ = lean_obj_once(&l_Lean_Meta_Sym_preprocessExpr___closed__3, &l_Lean_Meta_Sym_preprocessExpr___closed__3_once, _init_l_Lean_Meta_Sym_preprocessExpr___closed__3);
v___x_198_ = l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0(v___x_197_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v_a_200_; lean_object* v___x_201_; 
v___x_199_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(v_e_186_, v_a_190_);
v_a_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_a_200_);
lean_dec_ref(v___x_199_);
v___x_201_ = l_Lean_Meta_Sym_shareCommon(v_a_200_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
return v___x_201_;
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v_e_186_);
v_a_202_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_194_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_194_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessExpr___boxed(lean_object* v_e_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Meta_Sym_preprocessExpr(v_e_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_x_221_, lean_object* v_x_222_){
_start:
{
lean_object* v_ks_223_; lean_object* v_vs_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_248_; 
v_ks_223_ = lean_ctor_get(v_x_219_, 0);
v_vs_224_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_248_ == 0)
{
v___x_226_ = v_x_219_;
v_isShared_227_ = v_isSharedCheck_248_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_vs_224_);
lean_inc(v_ks_223_);
lean_dec(v_x_219_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_248_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_array_get_size(v_ks_223_);
v___x_229_ = lean_nat_dec_lt(v_x_220_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec(v_x_220_);
v___x_230_ = lean_array_push(v_ks_223_, v_x_221_);
v___x_231_ = lean_array_push(v_vs_224_, v_x_222_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_231_);
lean_ctor_set(v___x_226_, 0, v___x_230_);
v___x_233_ = v___x_226_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
else
{
lean_object* v_k_x27_235_; uint8_t v___x_236_; 
v_k_x27_235_ = lean_array_fget_borrowed(v_ks_223_, v_x_220_);
v___x_236_ = l_Lean_instBEqFVarId_beq(v_x_221_, v_k_x27_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_238_; 
if (v_isShared_227_ == 0)
{
v___x_238_ = v___x_226_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_ks_223_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_vs_224_);
v___x_238_ = v_reuseFailAlloc_242_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_x_220_, v___x_239_);
lean_dec(v_x_220_);
v_x_219_ = v___x_238_;
v_x_220_ = v___x_240_;
goto _start;
}
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_243_ = lean_array_fset(v_ks_223_, v_x_220_, v_x_221_);
v___x_244_ = lean_array_fset(v_vs_224_, v_x_220_, v_x_222_);
lean_dec(v_x_220_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_244_);
lean_ctor_set(v___x_226_, 0, v___x_243_);
v___x_246_ = v___x_226_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(lean_object* v_n_249_, lean_object* v_k_250_, lean_object* v_v_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_n_249_, v___x_252_, v_k_250_, v_v_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(lean_object* v_x_255_, size_t v_x_256_, size_t v_x_257_, lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
lean_object* v_es_260_; size_t v___x_261_; size_t v___x_262_; lean_object* v_j_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_es_260_ = lean_ctor_get(v_x_255_, 0);
v___x_261_ = ((size_t)31ULL);
v___x_262_ = lean_usize_land(v_x_256_, v___x_261_);
v_j_263_ = lean_usize_to_nat(v___x_262_);
v___x_264_ = lean_array_get_size(v_es_260_);
v___x_265_ = lean_nat_dec_lt(v_j_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_dec(v_j_263_);
lean_dec(v_x_259_);
lean_dec(v_x_258_);
return v_x_255_;
}
else
{
lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_304_; 
lean_inc_ref(v_es_260_);
v_isSharedCheck_304_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v_x_255_, 0);
lean_dec(v_unused_305_);
v___x_267_ = v_x_255_;
v_isShared_268_ = v_isSharedCheck_304_;
goto v_resetjp_266_;
}
else
{
lean_dec(v_x_255_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_304_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v_v_269_; lean_object* v___x_270_; lean_object* v_xs_x27_271_; lean_object* v___y_273_; 
v_v_269_ = lean_array_fget(v_es_260_, v_j_263_);
v___x_270_ = lean_box(0);
v_xs_x27_271_ = lean_array_fset(v_es_260_, v_j_263_, v___x_270_);
switch(lean_obj_tag(v_v_269_))
{
case 0:
{
lean_object* v_key_278_; lean_object* v_val_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_289_; 
v_key_278_ = lean_ctor_get(v_v_269_, 0);
v_val_279_ = lean_ctor_get(v_v_269_, 1);
v_isSharedCheck_289_ = !lean_is_exclusive(v_v_269_);
if (v_isSharedCheck_289_ == 0)
{
v___x_281_ = v_v_269_;
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_val_279_);
lean_inc(v_key_278_);
lean_dec(v_v_269_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
uint8_t v___x_283_; 
v___x_283_ = l_Lean_instBEqFVarId_beq(v_x_258_, v_key_278_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
lean_del_object(v___x_281_);
v___x_284_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_278_, v_val_279_, v_x_258_, v_x_259_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
v___y_273_ = v___x_285_;
goto v___jp_272_;
}
else
{
lean_object* v___x_287_; 
lean_dec(v_val_279_);
lean_dec(v_key_278_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v_x_259_);
lean_ctor_set(v___x_281_, 0, v_x_258_);
v___x_287_ = v___x_281_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_x_258_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_x_259_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
v___y_273_ = v___x_287_;
goto v___jp_272_;
}
}
}
}
case 1:
{
lean_object* v_node_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_302_; 
v_node_290_ = lean_ctor_get(v_v_269_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v_v_269_);
if (v_isSharedCheck_302_ == 0)
{
v___x_292_ = v_v_269_;
v_isShared_293_ = v_isSharedCheck_302_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_node_290_);
lean_dec(v_v_269_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_302_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
size_t v___x_294_; size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_294_ = ((size_t)5ULL);
v___x_295_ = lean_usize_shift_right(v_x_256_, v___x_294_);
v___x_296_ = ((size_t)1ULL);
v___x_297_ = lean_usize_add(v_x_257_, v___x_296_);
v___x_298_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_node_290_, v___x_295_, v___x_297_, v_x_258_, v_x_259_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_298_);
v___x_300_ = v___x_292_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
v___y_273_ = v___x_300_;
goto v___jp_272_;
}
}
}
default: 
{
lean_object* v___x_303_; 
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_x_258_);
lean_ctor_set(v___x_303_, 1, v_x_259_);
v___y_273_ = v___x_303_;
goto v___jp_272_;
}
}
v___jp_272_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = lean_array_fset(v_xs_x27_271_, v_j_263_, v___y_273_);
lean_dec(v_j_263_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_274_);
v___x_276_ = v___x_267_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
else
{
lean_object* v_ks_306_; lean_object* v_vs_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_325_; 
v_ks_306_ = lean_ctor_get(v_x_255_, 0);
v_vs_307_ = lean_ctor_get(v_x_255_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_325_ == 0)
{
v___x_309_ = v_x_255_;
v_isShared_310_ = v_isSharedCheck_325_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_vs_307_);
lean_inc(v_ks_306_);
lean_dec(v_x_255_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_325_;
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
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_ks_306_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_vs_307_);
v___x_312_ = v_reuseFailAlloc_324_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v_newNode_313_; size_t v___x_314_; uint8_t v___x_315_; 
v_newNode_313_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v___x_312_, v_x_258_, v_x_259_);
v___x_314_ = ((size_t)7ULL);
v___x_315_ = lean_usize_dec_le(v___x_314_, v_x_257_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_316_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_313_);
v___x_317_ = lean_unsigned_to_nat(4u);
v___x_318_ = lean_nat_dec_lt(v___x_316_, v___x_317_);
lean_dec(v___x_316_);
if (v___x_318_ == 0)
{
lean_object* v_ks_319_; lean_object* v_vs_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_ks_319_ = lean_ctor_get(v_newNode_313_, 0);
lean_inc_ref(v_ks_319_);
v_vs_320_ = lean_ctor_get(v_newNode_313_, 1);
lean_inc_ref(v_vs_320_);
lean_dec_ref(v_newNode_313_);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0);
v___x_323_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_x_257_, v_ks_319_, v_vs_320_, v___x_321_, v___x_322_);
lean_dec_ref(v_vs_320_);
lean_dec_ref(v_ks_319_);
return v___x_323_;
}
else
{
return v_newNode_313_;
}
}
else
{
return v_newNode_313_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(size_t v_depth_326_, lean_object* v_keys_327_, lean_object* v_vals_328_, lean_object* v_i_329_, lean_object* v_entries_330_){
_start:
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = lean_array_get_size(v_keys_327_);
v___x_332_ = lean_nat_dec_lt(v_i_329_, v___x_331_);
if (v___x_332_ == 0)
{
lean_dec(v_i_329_);
return v_entries_330_;
}
else
{
lean_object* v_k_333_; lean_object* v_v_334_; uint64_t v___x_335_; size_t v_h_336_; size_t v___x_337_; lean_object* v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v_h_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_k_333_ = lean_array_fget_borrowed(v_keys_327_, v_i_329_);
v_v_334_ = lean_array_fget_borrowed(v_vals_328_, v_i_329_);
v___x_335_ = l_Lean_instHashableFVarId_hash(v_k_333_);
v_h_336_ = lean_uint64_to_usize(v___x_335_);
v___x_337_ = ((size_t)5ULL);
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_sub(v_depth_326_, v___x_339_);
v___x_341_ = lean_usize_mul(v___x_337_, v___x_340_);
v_h_342_ = lean_usize_shift_right(v_h_336_, v___x_341_);
v___x_343_ = lean_nat_add(v_i_329_, v___x_338_);
lean_dec(v_i_329_);
lean_inc(v_v_334_);
lean_inc(v_k_333_);
v___x_344_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_entries_330_, v_h_342_, v_depth_326_, v_k_333_, v_v_334_);
v_i_329_ = v___x_343_;
v_entries_330_ = v___x_344_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_346_, lean_object* v_keys_347_, lean_object* v_vals_348_, lean_object* v_i_349_, lean_object* v_entries_350_){
_start:
{
size_t v_depth_boxed_351_; lean_object* v_res_352_; 
v_depth_boxed_351_ = lean_unbox_usize(v_depth_346_);
lean_dec(v_depth_346_);
v_res_352_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_boxed_351_, v_keys_347_, v_vals_348_, v_i_349_, v_entries_350_);
lean_dec_ref(v_vals_348_);
lean_dec_ref(v_keys_347_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___boxed(lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
size_t v_x_9203__boxed_358_; size_t v_x_9204__boxed_359_; lean_object* v_res_360_; 
v_x_9203__boxed_358_ = lean_unbox_usize(v_x_354_);
lean_dec(v_x_354_);
v_x_9204__boxed_359_ = lean_unbox_usize(v_x_355_);
lean_dec(v_x_355_);
v_res_360_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_353_, v_x_9203__boxed_358_, v_x_9204__boxed_359_, v_x_356_, v_x_357_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
uint64_t v___x_364_; size_t v___x_365_; size_t v___x_366_; lean_object* v___x_367_; 
v___x_364_ = l_Lean_instHashableFVarId_hash(v_x_362_);
v___x_365_ = lean_uint64_to_usize(v___x_364_);
v___x_366_ = ((size_t)1ULL);
v___x_367_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_361_, v___x_365_, v___x_366_, v_x_362_, v_x_363_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(lean_object* v_as_368_, size_t v_sz_369_, size_t v_i_370_, lean_object* v_b_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = lean_usize_dec_lt(v_i_370_, v_sz_369_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; 
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v_b_371_);
return v___x_380_;
}
else
{
lean_object* v_snd_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_486_; 
v_snd_381_ = lean_ctor_get(v_b_371_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_b_371_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v_b_371_, 0);
lean_dec(v_unused_487_);
v___x_383_ = v_b_371_;
v_isShared_384_ = v_isSharedCheck_486_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_snd_381_);
lean_dec(v_b_371_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_486_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v_a_387_; lean_object* v_a_394_; 
v___x_385_ = lean_box(0);
v_a_394_ = lean_array_uget(v_as_368_, v_i_370_);
if (lean_obj_tag(v_a_394_) == 0)
{
v_a_387_ = v_snd_381_;
goto v___jp_386_;
}
else
{
lean_object* v_snd_395_; lean_object* v_val_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_485_; 
v_snd_395_ = lean_ctor_get(v_snd_381_, 1);
lean_inc(v_snd_395_);
v_val_396_ = lean_ctor_get(v_a_394_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v_a_394_);
if (v_isSharedCheck_485_ == 0)
{
v___x_398_ = v_a_394_;
v_isShared_399_ = v_isSharedCheck_485_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_val_396_);
lean_dec(v_a_394_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_485_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_fst_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_483_; 
v_fst_400_ = lean_ctor_get(v_snd_381_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v_snd_381_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v_snd_381_, 1);
lean_dec(v_unused_484_);
v___x_402_ = v_snd_381_;
v_isShared_403_ = v_isSharedCheck_483_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_fst_400_);
lean_dec(v_snd_381_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_483_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_fst_404_; lean_object* v_snd_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_482_; 
v_fst_404_ = lean_ctor_get(v_snd_395_, 0);
v_snd_405_ = lean_ctor_get(v_snd_395_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_snd_395_);
if (v_isSharedCheck_482_ == 0)
{
v___x_407_ = v_snd_395_;
v_isShared_408_ = v_isSharedCheck_482_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_snd_405_);
lean_inc(v_fst_404_);
lean_dec(v_snd_395_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_482_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v_decl_410_; 
if (lean_obj_tag(v_val_396_) == 0)
{
lean_object* v_fvarId_425_; lean_object* v_userName_426_; lean_object* v_type_427_; uint8_t v_bi_428_; uint8_t v_kind_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_446_; 
v_fvarId_425_ = lean_ctor_get(v_val_396_, 1);
v_userName_426_ = lean_ctor_get(v_val_396_, 2);
v_type_427_ = lean_ctor_get(v_val_396_, 3);
v_bi_428_ = lean_ctor_get_uint8(v_val_396_, sizeof(void*)*4);
v_kind_429_ = lean_ctor_get_uint8(v_val_396_, sizeof(void*)*4 + 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_val_396_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v_val_396_, 0);
lean_dec(v_unused_447_);
v___x_431_ = v_val_396_;
v_isShared_432_ = v_isSharedCheck_446_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_type_427_);
lean_inc(v_userName_426_);
lean_inc(v_fvarId_425_);
lean_dec(v_val_396_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_446_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_Sym_preprocessExpr(v_type_427_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
lean_inc(v_snd_405_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 3, v_a_434_);
lean_ctor_set(v___x_431_, 0, v_snd_405_);
v___x_436_ = v___x_431_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_snd_405_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_fvarId_425_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_userName_426_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_a_434_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*4, v_bi_428_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*4 + 1, v_kind_429_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
v_decl_410_ = v___x_436_;
goto v___jp_409_;
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_del_object(v___x_431_);
lean_dec(v_userName_426_);
lean_dec(v_fvarId_425_);
lean_del_object(v___x_407_);
lean_dec(v_snd_405_);
lean_dec(v_fst_404_);
lean_del_object(v___x_402_);
lean_dec(v_fst_400_);
lean_del_object(v___x_398_);
lean_del_object(v___x_383_);
v_a_438_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_433_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_433_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
else
{
lean_object* v_fvarId_448_; lean_object* v_userName_449_; lean_object* v_type_450_; lean_object* v_value_451_; uint8_t v_nondep_452_; uint8_t v_kind_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_480_; 
v_fvarId_448_ = lean_ctor_get(v_val_396_, 1);
v_userName_449_ = lean_ctor_get(v_val_396_, 2);
v_type_450_ = lean_ctor_get(v_val_396_, 3);
v_value_451_ = lean_ctor_get(v_val_396_, 4);
v_nondep_452_ = lean_ctor_get_uint8(v_val_396_, sizeof(void*)*5);
v_kind_453_ = lean_ctor_get_uint8(v_val_396_, sizeof(void*)*5 + 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_val_396_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; 
v_unused_481_ = lean_ctor_get(v_val_396_, 0);
lean_dec(v_unused_481_);
v___x_455_ = v_val_396_;
v_isShared_456_ = v_isSharedCheck_480_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_value_451_);
lean_inc(v_type_450_);
lean_inc(v_userName_449_);
lean_inc(v_fvarId_448_);
lean_dec(v_val_396_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_480_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Meta_Sym_preprocessExpr(v_type_450_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
v___x_459_ = l_Lean_Meta_Sym_preprocessExpr(v_value_451_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_462_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 1);
lean_inc(v_snd_405_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_a_460_);
lean_ctor_set(v___x_455_, 3, v_a_458_);
lean_ctor_set(v___x_455_, 0, v_snd_405_);
v___x_462_ = v___x_455_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_snd_405_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_fvarId_448_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_userName_449_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_a_458_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_a_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*5, v_nondep_452_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*5 + 1, v_kind_453_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
v_decl_410_ = v___x_462_;
goto v___jp_409_;
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec(v_a_458_);
lean_del_object(v___x_455_);
lean_dec(v_userName_449_);
lean_dec(v_fvarId_448_);
lean_del_object(v___x_407_);
lean_dec(v_snd_405_);
lean_dec(v_fst_404_);
lean_del_object(v___x_402_);
lean_dec(v_fst_400_);
lean_del_object(v___x_398_);
lean_del_object(v___x_383_);
v_a_464_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_459_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_459_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_del_object(v___x_455_);
lean_dec_ref(v_value_451_);
lean_dec(v_userName_449_);
lean_dec(v_fvarId_448_);
lean_del_object(v___x_407_);
lean_dec(v_snd_405_);
lean_dec(v_fst_404_);
lean_del_object(v___x_402_);
lean_dec(v_fst_400_);
lean_del_object(v___x_398_);
lean_del_object(v___x_383_);
v_a_472_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_457_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_457_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
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
v___jp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_nat_add(v_snd_405_, v___x_411_);
lean_dec(v_snd_405_);
lean_inc_ref(v_decl_410_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v_decl_410_);
v___x_414_ = v___x_398_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_decl_410_);
v___x_414_ = v_reuseFailAlloc_424_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_415_ = l_Lean_PersistentArray_push___redArg(v_fst_404_, v___x_414_);
v___x_416_ = l_Lean_LocalDecl_fvarId(v_decl_410_);
v___x_417_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_400_, v___x_416_, v_decl_410_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 1, v___x_412_);
lean_ctor_set(v___x_407_, 0, v___x_415_);
v___x_419_ = v___x_407_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_412_);
v___x_419_ = v_reuseFailAlloc_423_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_421_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 1, v___x_419_);
lean_ctor_set(v___x_402_, 0, v___x_417_);
v___x_421_ = v___x_402_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
v_a_387_ = v___x_421_;
goto v___jp_386_;
}
}
}
}
}
}
}
}
v___jp_386_:
{
lean_object* v___x_389_; 
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v_a_387_);
lean_ctor_set(v___x_383_, 0, v___x_385_);
v___x_389_ = v___x_383_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_a_387_);
v___x_389_ = v_reuseFailAlloc_393_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
size_t v___x_390_; size_t v___x_391_; 
v___x_390_ = ((size_t)1ULL);
v___x_391_ = lean_usize_add(v_i_370_, v___x_390_);
v_i_370_ = v___x_391_;
v_b_371_ = v___x_389_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_as_488_, lean_object* v_sz_489_, lean_object* v_i_490_, lean_object* v_b_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
size_t v_sz_boxed_499_; size_t v_i_boxed_500_; lean_object* v_res_501_; 
v_sz_boxed_499_ = lean_unbox_usize(v_sz_489_);
lean_dec(v_sz_489_);
v_i_boxed_500_ = lean_unbox_usize(v_i_490_);
lean_dec(v_i_490_);
v_res_501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_488_, v_sz_boxed_499_, v_i_boxed_500_, v_b_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec_ref(v_as_488_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(lean_object* v_as_502_, size_t v_sz_503_, size_t v_i_504_, lean_object* v_b_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
uint8_t v___x_513_; 
v___x_513_ = lean_usize_dec_lt(v_i_504_, v_sz_503_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v_b_505_);
return v___x_514_;
}
else
{
lean_object* v_snd_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_620_; 
v_snd_515_ = lean_ctor_get(v_b_505_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v_b_505_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v_b_505_, 0);
lean_dec(v_unused_621_);
v___x_517_ = v_b_505_;
v_isShared_518_ = v_isSharedCheck_620_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_snd_515_);
lean_dec(v_b_505_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_620_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v_a_521_; lean_object* v_a_528_; 
v___x_519_ = lean_box(0);
v_a_528_ = lean_array_uget(v_as_502_, v_i_504_);
if (lean_obj_tag(v_a_528_) == 0)
{
v_a_521_ = v_snd_515_;
goto v___jp_520_;
}
else
{
lean_object* v_snd_529_; lean_object* v_val_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_619_; 
v_snd_529_ = lean_ctor_get(v_snd_515_, 1);
lean_inc(v_snd_529_);
v_val_530_ = lean_ctor_get(v_a_528_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_a_528_);
if (v_isSharedCheck_619_ == 0)
{
v___x_532_ = v_a_528_;
v_isShared_533_ = v_isSharedCheck_619_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_val_530_);
lean_dec(v_a_528_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_619_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_fst_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_617_; 
v_fst_534_ = lean_ctor_get(v_snd_515_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v_snd_515_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v_snd_515_, 1);
lean_dec(v_unused_618_);
v___x_536_ = v_snd_515_;
v_isShared_537_ = v_isSharedCheck_617_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_fst_534_);
lean_dec(v_snd_515_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_617_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_fst_538_; lean_object* v_snd_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_616_; 
v_fst_538_ = lean_ctor_get(v_snd_529_, 0);
v_snd_539_ = lean_ctor_get(v_snd_529_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v_snd_529_);
if (v_isSharedCheck_616_ == 0)
{
v___x_541_ = v_snd_529_;
v_isShared_542_ = v_isSharedCheck_616_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_snd_539_);
lean_inc(v_fst_538_);
lean_dec(v_snd_529_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_616_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_decl_544_; 
if (lean_obj_tag(v_val_530_) == 0)
{
lean_object* v_fvarId_559_; lean_object* v_userName_560_; lean_object* v_type_561_; uint8_t v_bi_562_; uint8_t v_kind_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_580_; 
v_fvarId_559_ = lean_ctor_get(v_val_530_, 1);
v_userName_560_ = lean_ctor_get(v_val_530_, 2);
v_type_561_ = lean_ctor_get(v_val_530_, 3);
v_bi_562_ = lean_ctor_get_uint8(v_val_530_, sizeof(void*)*4);
v_kind_563_ = lean_ctor_get_uint8(v_val_530_, sizeof(void*)*4 + 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_val_530_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v_val_530_, 0);
lean_dec(v_unused_581_);
v___x_565_ = v_val_530_;
v_isShared_566_ = v_isSharedCheck_580_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_type_561_);
lean_inc(v_userName_560_);
lean_inc(v_fvarId_559_);
lean_dec(v_val_530_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_580_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Meta_Sym_preprocessExpr(v_type_561_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_567_, 1);
lean_inc(v_snd_539_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 3, v_a_568_);
lean_ctor_set(v___x_565_, 0, v_snd_539_);
v___x_570_ = v___x_565_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_snd_539_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_fvarId_559_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_userName_560_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_a_568_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, sizeof(void*)*4, v_bi_562_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, sizeof(void*)*4 + 1, v_kind_563_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
v_decl_544_ = v___x_570_;
goto v___jp_543_;
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_del_object(v___x_565_);
lean_dec(v_userName_560_);
lean_dec(v_fvarId_559_);
lean_del_object(v___x_541_);
lean_dec(v_snd_539_);
lean_dec(v_fst_538_);
lean_del_object(v___x_536_);
lean_dec(v_fst_534_);
lean_del_object(v___x_532_);
lean_del_object(v___x_517_);
v_a_572_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_567_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_567_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
else
{
lean_object* v_fvarId_582_; lean_object* v_userName_583_; lean_object* v_type_584_; lean_object* v_value_585_; uint8_t v_nondep_586_; uint8_t v_kind_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_614_; 
v_fvarId_582_ = lean_ctor_get(v_val_530_, 1);
v_userName_583_ = lean_ctor_get(v_val_530_, 2);
v_type_584_ = lean_ctor_get(v_val_530_, 3);
v_value_585_ = lean_ctor_get(v_val_530_, 4);
v_nondep_586_ = lean_ctor_get_uint8(v_val_530_, sizeof(void*)*5);
v_kind_587_ = lean_ctor_get_uint8(v_val_530_, sizeof(void*)*5 + 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_val_530_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v_val_530_, 0);
lean_dec(v_unused_615_);
v___x_589_ = v_val_530_;
v_isShared_590_ = v_isSharedCheck_614_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_value_585_);
lean_inc(v_type_584_);
lean_inc(v_userName_583_);
lean_inc(v_fvarId_582_);
lean_dec(v_val_530_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_614_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Meta_Sym_preprocessExpr(v_type_584_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_593_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v___x_593_ = l_Lean_Meta_Sym_preprocessExpr(v_value_585_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_596_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
lean_inc(v_snd_539_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 4, v_a_594_);
lean_ctor_set(v___x_589_, 3, v_a_592_);
lean_ctor_set(v___x_589_, 0, v_snd_539_);
v___x_596_ = v___x_589_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_snd_539_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_fvarId_582_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_userName_583_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_a_592_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v_a_594_);
lean_ctor_set_uint8(v_reuseFailAlloc_597_, sizeof(void*)*5, v_nondep_586_);
lean_ctor_set_uint8(v_reuseFailAlloc_597_, sizeof(void*)*5 + 1, v_kind_587_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
v_decl_544_ = v___x_596_;
goto v___jp_543_;
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_a_592_);
lean_del_object(v___x_589_);
lean_dec(v_userName_583_);
lean_dec(v_fvarId_582_);
lean_del_object(v___x_541_);
lean_dec(v_snd_539_);
lean_dec(v_fst_538_);
lean_del_object(v___x_536_);
lean_dec(v_fst_534_);
lean_del_object(v___x_532_);
lean_del_object(v___x_517_);
v_a_598_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_593_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_593_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_del_object(v___x_589_);
lean_dec_ref(v_value_585_);
lean_dec(v_userName_583_);
lean_dec(v_fvarId_582_);
lean_del_object(v___x_541_);
lean_dec(v_snd_539_);
lean_dec(v_fst_538_);
lean_del_object(v___x_536_);
lean_dec(v_fst_534_);
lean_del_object(v___x_532_);
lean_del_object(v___x_517_);
v_a_606_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_591_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_591_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
v___jp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = lean_nat_add(v_snd_539_, v___x_545_);
lean_dec(v_snd_539_);
lean_inc_ref(v_decl_544_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v_decl_544_);
v___x_548_ = v___x_532_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_decl_544_);
v___x_548_ = v_reuseFailAlloc_558_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_549_ = l_Lean_PersistentArray_push___redArg(v_fst_538_, v___x_548_);
v___x_550_ = l_Lean_LocalDecl_fvarId(v_decl_544_);
v___x_551_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_534_, v___x_550_, v_decl_544_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_546_);
lean_ctor_set(v___x_541_, 0, v___x_549_);
v___x_553_ = v___x_541_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_546_);
v___x_553_ = v_reuseFailAlloc_557_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v___x_553_);
lean_ctor_set(v___x_536_, 0, v___x_551_);
v___x_555_ = v___x_536_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
v_a_521_ = v___x_555_;
goto v___jp_520_;
}
}
}
}
}
}
}
}
v___jp_520_:
{
lean_object* v___x_523_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 1, v_a_521_);
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_523_ = v___x_517_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_a_521_);
v___x_523_ = v_reuseFailAlloc_527_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
size_t v___x_524_; size_t v___x_525_; lean_object* v___x_526_; 
v___x_524_ = ((size_t)1ULL);
v___x_525_ = lean_usize_add(v_i_504_, v___x_524_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_502_, v_sz_503_, v___x_525_, v___x_523_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
return v___x_526_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6___boxed(lean_object* v_as_622_, lean_object* v_sz_623_, lean_object* v_i_624_, lean_object* v_b_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
size_t v_sz_boxed_633_; size_t v_i_boxed_634_; lean_object* v_res_635_; 
v_sz_boxed_633_ = lean_unbox_usize(v_sz_623_);
lean_dec(v_sz_623_);
v_i_boxed_634_ = lean_unbox_usize(v_i_624_);
lean_dec(v_i_624_);
v_res_635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_as_622_, v_sz_boxed_633_, v_i_boxed_634_, v_b_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec_ref(v_as_622_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(lean_object* v_init_636_, lean_object* v_n_637_, lean_object* v_b_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
if (lean_obj_tag(v_n_637_) == 0)
{
lean_object* v_cs_646_; lean_object* v___x_647_; lean_object* v___x_648_; size_t v_sz_649_; size_t v___x_650_; lean_object* v___x_651_; 
v_cs_646_ = lean_ctor_get(v_n_637_, 0);
v___x_647_ = lean_box(0);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v_b_638_);
v_sz_649_ = lean_array_size(v_cs_646_);
v___x_650_ = ((size_t)0ULL);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_636_, v_cs_646_, v_sz_649_, v___x_650_, v___x_648_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_666_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_666_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_666_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_666_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_fst_656_; 
v_fst_656_ = lean_ctor_get(v_a_652_, 0);
if (lean_obj_tag(v_fst_656_) == 0)
{
lean_object* v_snd_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v_snd_657_ = lean_ctor_get(v_a_652_, 1);
lean_inc(v_snd_657_);
lean_dec(v_a_652_);
v___x_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_658_, 0, v_snd_657_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_658_);
v___x_660_ = v___x_654_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
else
{
lean_object* v_val_662_; lean_object* v___x_664_; 
lean_inc_ref(v_fst_656_);
lean_dec(v_a_652_);
v_val_662_ = lean_ctor_get(v_fst_656_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v_fst_656_, 1);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v_val_662_);
v___x_664_ = v___x_654_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_val_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
v_a_667_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_651_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_651_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v_vs_675_; lean_object* v___x_676_; lean_object* v___x_677_; size_t v_sz_678_; size_t v___x_679_; lean_object* v___x_680_; 
v_vs_675_ = lean_ctor_get(v_n_637_, 0);
v___x_676_ = lean_box(0);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v_b_638_);
v_sz_678_ = lean_array_size(v_vs_675_);
v___x_679_ = ((size_t)0ULL);
v___x_680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_vs_675_, v_sz_678_, v___x_679_, v___x_677_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_695_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_695_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_695_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_695_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v_fst_685_; 
v_fst_685_ = lean_ctor_get(v_a_681_, 0);
if (lean_obj_tag(v_fst_685_) == 0)
{
lean_object* v_snd_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
v_snd_686_ = lean_ctor_get(v_a_681_, 1);
lean_inc(v_snd_686_);
lean_dec(v_a_681_);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v_snd_686_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_687_);
v___x_689_ = v___x_683_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
else
{
lean_object* v_val_691_; lean_object* v___x_693_; 
lean_inc_ref(v_fst_685_);
lean_dec(v_a_681_);
v_val_691_ = lean_ctor_get(v_fst_685_, 0);
lean_inc(v_val_691_);
lean_dec_ref_known(v_fst_685_, 1);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v_val_691_);
v___x_693_ = v___x_683_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_val_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_a_696_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_680_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_680_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(lean_object* v_init_704_, lean_object* v_as_705_, size_t v_sz_706_, size_t v_i_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = lean_usize_dec_lt(v_i_707_, v_sz_706_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_b_708_);
return v___x_717_;
}
else
{
lean_object* v_snd_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_752_; 
v_snd_718_ = lean_ctor_get(v_b_708_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v_b_708_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v_b_708_, 0);
lean_dec(v_unused_753_);
v___x_720_ = v_b_708_;
v_isShared_721_ = v_isSharedCheck_752_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_snd_718_);
lean_dec(v_b_708_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_752_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v_a_723_; lean_object* v___x_724_; 
v___x_722_ = lean_box(0);
v_a_723_ = lean_array_uget_borrowed(v_as_705_, v_i_707_);
lean_inc(v_snd_718_);
v___x_724_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_704_, v_a_723_, v_snd_718_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_743_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_743_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_743_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_743_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
if (lean_obj_tag(v_a_725_) == 0)
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v_a_725_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_729_);
v___x_731_ = v___x_720_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_snd_718_);
v___x_731_ = v_reuseFailAlloc_735_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_733_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_731_);
v___x_733_ = v___x_727_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; 
lean_del_object(v___x_727_);
lean_dec(v_snd_718_);
v_a_736_ = lean_ctor_get(v_a_725_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v_a_725_, 1);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v_a_736_);
lean_ctor_set(v___x_720_, 0, v___x_722_);
v___x_738_ = v___x_720_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_a_736_);
v___x_738_ = v_reuseFailAlloc_742_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
size_t v___x_739_; size_t v___x_740_; 
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_add(v_i_707_, v___x_739_);
v_i_707_ = v___x_740_;
v_b_708_ = v___x_738_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_del_object(v___x_720_);
lean_dec(v_snd_718_);
v_a_744_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_724_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_724_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_init_754_, lean_object* v_as_755_, lean_object* v_sz_756_, lean_object* v_i_757_, lean_object* v_b_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
size_t v_sz_boxed_766_; size_t v_i_boxed_767_; lean_object* v_res_768_; 
v_sz_boxed_766_ = lean_unbox_usize(v_sz_756_);
lean_dec(v_sz_756_);
v_i_boxed_767_ = lean_unbox_usize(v_i_757_);
lean_dec(v_i_757_);
v_res_768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_754_, v_as_755_, v_sz_boxed_766_, v_i_boxed_767_, v_b_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec_ref(v_as_755_);
lean_dec_ref(v_init_754_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2___boxed(lean_object* v_init_769_, lean_object* v_n_770_, lean_object* v_b_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_769_, v_n_770_, v_b_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec_ref(v_n_770_);
lean_dec_ref(v_init_769_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(lean_object* v_as_780_, size_t v_sz_781_, size_t v_i_782_, lean_object* v_b_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
uint8_t v___x_791_; 
v___x_791_ = lean_usize_dec_lt(v_i_782_, v_sz_781_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v_b_783_);
return v___x_792_;
}
else
{
lean_object* v_snd_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_898_; 
v_snd_793_ = lean_ctor_get(v_b_783_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_b_783_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_b_783_, 0);
lean_dec(v_unused_899_);
v___x_795_ = v_b_783_;
v_isShared_796_ = v_isSharedCheck_898_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snd_793_);
lean_dec(v_b_783_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_898_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v_a_799_; lean_object* v_a_806_; 
v___x_797_ = lean_box(0);
v_a_806_ = lean_array_uget(v_as_780_, v_i_782_);
if (lean_obj_tag(v_a_806_) == 0)
{
v_a_799_ = v_snd_793_;
goto v___jp_798_;
}
else
{
lean_object* v_snd_807_; lean_object* v_val_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_897_; 
v_snd_807_ = lean_ctor_get(v_snd_793_, 1);
lean_inc(v_snd_807_);
v_val_808_ = lean_ctor_get(v_a_806_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_a_806_);
if (v_isSharedCheck_897_ == 0)
{
v___x_810_ = v_a_806_;
v_isShared_811_ = v_isSharedCheck_897_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_val_808_);
lean_dec(v_a_806_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_897_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_fst_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_895_; 
v_fst_812_ = lean_ctor_get(v_snd_793_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v_snd_793_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v_snd_793_, 1);
lean_dec(v_unused_896_);
v___x_814_ = v_snd_793_;
v_isShared_815_ = v_isSharedCheck_895_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_fst_812_);
lean_dec(v_snd_793_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_895_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_fst_816_; lean_object* v_snd_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_894_; 
v_fst_816_ = lean_ctor_get(v_snd_807_, 0);
v_snd_817_ = lean_ctor_get(v_snd_807_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_snd_807_);
if (v_isSharedCheck_894_ == 0)
{
v___x_819_ = v_snd_807_;
v_isShared_820_ = v_isSharedCheck_894_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_snd_817_);
lean_inc(v_fst_816_);
lean_dec(v_snd_807_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_894_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v_decl_822_; 
if (lean_obj_tag(v_val_808_) == 0)
{
lean_object* v_fvarId_837_; lean_object* v_userName_838_; lean_object* v_type_839_; uint8_t v_bi_840_; uint8_t v_kind_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_858_; 
v_fvarId_837_ = lean_ctor_get(v_val_808_, 1);
v_userName_838_ = lean_ctor_get(v_val_808_, 2);
v_type_839_ = lean_ctor_get(v_val_808_, 3);
v_bi_840_ = lean_ctor_get_uint8(v_val_808_, sizeof(void*)*4);
v_kind_841_ = lean_ctor_get_uint8(v_val_808_, sizeof(void*)*4 + 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_val_808_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_val_808_, 0);
lean_dec(v_unused_859_);
v___x_843_ = v_val_808_;
v_isShared_844_ = v_isSharedCheck_858_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_type_839_);
lean_inc(v_userName_838_);
lean_inc(v_fvarId_837_);
lean_dec(v_val_808_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_858_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Meta_Sym_preprocessExpr(v_type_839_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
lean_inc(v_snd_817_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 3, v_a_846_);
lean_ctor_set(v___x_843_, 0, v_snd_817_);
v___x_848_ = v___x_843_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_snd_817_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_fvarId_837_);
lean_ctor_set(v_reuseFailAlloc_849_, 2, v_userName_838_);
lean_ctor_set(v_reuseFailAlloc_849_, 3, v_a_846_);
lean_ctor_set_uint8(v_reuseFailAlloc_849_, sizeof(void*)*4, v_bi_840_);
lean_ctor_set_uint8(v_reuseFailAlloc_849_, sizeof(void*)*4 + 1, v_kind_841_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
v_decl_822_ = v___x_848_;
goto v___jp_821_;
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_del_object(v___x_843_);
lean_dec(v_userName_838_);
lean_dec(v_fvarId_837_);
lean_del_object(v___x_819_);
lean_dec(v_snd_817_);
lean_dec(v_fst_816_);
lean_del_object(v___x_814_);
lean_dec(v_fst_812_);
lean_del_object(v___x_810_);
lean_del_object(v___x_795_);
v_a_850_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_845_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_845_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
else
{
lean_object* v_fvarId_860_; lean_object* v_userName_861_; lean_object* v_type_862_; lean_object* v_value_863_; uint8_t v_nondep_864_; uint8_t v_kind_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_892_; 
v_fvarId_860_ = lean_ctor_get(v_val_808_, 1);
v_userName_861_ = lean_ctor_get(v_val_808_, 2);
v_type_862_ = lean_ctor_get(v_val_808_, 3);
v_value_863_ = lean_ctor_get(v_val_808_, 4);
v_nondep_864_ = lean_ctor_get_uint8(v_val_808_, sizeof(void*)*5);
v_kind_865_ = lean_ctor_get_uint8(v_val_808_, sizeof(void*)*5 + 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v_val_808_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_val_808_, 0);
lean_dec(v_unused_893_);
v___x_867_ = v_val_808_;
v_isShared_868_ = v_isSharedCheck_892_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_value_863_);
lean_inc(v_type_862_);
lean_inc(v_userName_861_);
lean_inc(v_fvarId_860_);
lean_dec(v_val_808_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_892_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Meta_Sym_preprocessExpr(v_type_862_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_869_, 1);
v___x_871_ = l_Lean_Meta_Sym_preprocessExpr(v_value_863_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
lean_inc(v_snd_817_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v_a_872_);
lean_ctor_set(v___x_867_, 3, v_a_870_);
lean_ctor_set(v___x_867_, 0, v_snd_817_);
v___x_874_ = v___x_867_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_snd_817_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_fvarId_860_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_userName_861_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v_a_870_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v_a_872_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*5, v_nondep_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*5 + 1, v_kind_865_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
v_decl_822_ = v___x_874_;
goto v___jp_821_;
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_a_870_);
lean_del_object(v___x_867_);
lean_dec(v_userName_861_);
lean_dec(v_fvarId_860_);
lean_del_object(v___x_819_);
lean_dec(v_snd_817_);
lean_dec(v_fst_816_);
lean_del_object(v___x_814_);
lean_dec(v_fst_812_);
lean_del_object(v___x_810_);
lean_del_object(v___x_795_);
v_a_876_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_871_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_871_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_del_object(v___x_867_);
lean_dec_ref(v_value_863_);
lean_dec(v_userName_861_);
lean_dec(v_fvarId_860_);
lean_del_object(v___x_819_);
lean_dec(v_snd_817_);
lean_dec(v_fst_816_);
lean_del_object(v___x_814_);
lean_dec(v_fst_812_);
lean_del_object(v___x_810_);
lean_del_object(v___x_795_);
v_a_884_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_869_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_869_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
v___jp_821_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_nat_add(v_snd_817_, v___x_823_);
lean_dec(v_snd_817_);
lean_inc_ref(v_decl_822_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v_decl_822_);
v___x_826_ = v___x_810_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_decl_822_);
v___x_826_ = v_reuseFailAlloc_836_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_827_ = l_Lean_PersistentArray_push___redArg(v_fst_816_, v___x_826_);
v___x_828_ = l_Lean_LocalDecl_fvarId(v_decl_822_);
v___x_829_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_812_, v___x_828_, v_decl_822_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v___x_824_);
lean_ctor_set(v___x_819_, 0, v___x_827_);
v___x_831_ = v___x_819_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_824_);
v___x_831_ = v_reuseFailAlloc_835_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_833_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v___x_831_);
lean_ctor_set(v___x_814_, 0, v___x_829_);
v___x_833_ = v___x_814_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
v_a_799_ = v___x_833_;
goto v___jp_798_;
}
}
}
}
}
}
}
}
v___jp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v_a_799_);
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_801_ = v___x_795_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_a_799_);
v___x_801_ = v_reuseFailAlloc_805_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
size_t v___x_802_; size_t v___x_803_; 
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_add(v_i_782_, v___x_802_);
v_i_782_ = v___x_803_;
v_b_783_ = v___x_801_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8___boxed(lean_object* v_as_900_, lean_object* v_sz_901_, lean_object* v_i_902_, lean_object* v_b_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
size_t v_sz_boxed_911_; size_t v_i_boxed_912_; lean_object* v_res_913_; 
v_sz_boxed_911_ = lean_unbox_usize(v_sz_901_);
lean_dec(v_sz_901_);
v_i_boxed_912_ = lean_unbox_usize(v_i_902_);
lean_dec(v_i_902_);
v_res_913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_900_, v_sz_boxed_911_, v_i_boxed_912_, v_b_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec_ref(v_as_900_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(lean_object* v_as_914_, size_t v_sz_915_, size_t v_i_916_, lean_object* v_b_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
uint8_t v___x_925_; 
v___x_925_ = lean_usize_dec_lt(v_i_916_, v_sz_915_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v_b_917_);
return v___x_926_;
}
else
{
lean_object* v_snd_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_1032_; 
v_snd_927_ = lean_ctor_get(v_b_917_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_b_917_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v_b_917_, 0);
lean_dec(v_unused_1033_);
v___x_929_ = v_b_917_;
v_isShared_930_ = v_isSharedCheck_1032_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_snd_927_);
lean_dec(v_b_917_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_1032_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v_a_933_; lean_object* v_a_940_; 
v___x_931_ = lean_box(0);
v_a_940_ = lean_array_uget(v_as_914_, v_i_916_);
if (lean_obj_tag(v_a_940_) == 0)
{
v_a_933_ = v_snd_927_;
goto v___jp_932_;
}
else
{
lean_object* v_snd_941_; lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_1031_; 
v_snd_941_ = lean_ctor_get(v_snd_927_, 1);
lean_inc(v_snd_941_);
v_val_942_ = lean_ctor_get(v_a_940_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_a_940_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_944_ = v_a_940_;
v_isShared_945_ = v_isSharedCheck_1031_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v_a_940_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_1031_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_fst_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_1029_; 
v_fst_946_ = lean_ctor_get(v_snd_927_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_snd_927_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v_snd_927_, 1);
lean_dec(v_unused_1030_);
v___x_948_ = v_snd_927_;
v_isShared_949_ = v_isSharedCheck_1029_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_fst_946_);
lean_dec(v_snd_927_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_1029_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_fst_950_; lean_object* v_snd_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_1028_; 
v_fst_950_ = lean_ctor_get(v_snd_941_, 0);
v_snd_951_ = lean_ctor_get(v_snd_941_, 1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_snd_941_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_953_ = v_snd_941_;
v_isShared_954_ = v_isSharedCheck_1028_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_snd_951_);
lean_inc(v_fst_950_);
lean_dec(v_snd_941_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_1028_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_decl_956_; 
if (lean_obj_tag(v_val_942_) == 0)
{
lean_object* v_fvarId_971_; lean_object* v_userName_972_; lean_object* v_type_973_; uint8_t v_bi_974_; uint8_t v_kind_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_992_; 
v_fvarId_971_ = lean_ctor_get(v_val_942_, 1);
v_userName_972_ = lean_ctor_get(v_val_942_, 2);
v_type_973_ = lean_ctor_get(v_val_942_, 3);
v_bi_974_ = lean_ctor_get_uint8(v_val_942_, sizeof(void*)*4);
v_kind_975_ = lean_ctor_get_uint8(v_val_942_, sizeof(void*)*4 + 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_val_942_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; 
v_unused_993_ = lean_ctor_get(v_val_942_, 0);
lean_dec(v_unused_993_);
v___x_977_ = v_val_942_;
v_isShared_978_ = v_isSharedCheck_992_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_type_973_);
lean_inc(v_userName_972_);
lean_inc(v_fvarId_971_);
lean_dec(v_val_942_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_992_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_Meta_Sym_preprocessExpr(v_type_973_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
lean_inc(v_snd_951_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 3, v_a_980_);
lean_ctor_set(v___x_977_, 0, v_snd_951_);
v___x_982_ = v___x_977_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_snd_951_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_fvarId_971_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_userName_972_);
lean_ctor_set(v_reuseFailAlloc_983_, 3, v_a_980_);
lean_ctor_set_uint8(v_reuseFailAlloc_983_, sizeof(void*)*4, v_bi_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_983_, sizeof(void*)*4 + 1, v_kind_975_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
v_decl_956_ = v___x_982_;
goto v___jp_955_;
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_del_object(v___x_977_);
lean_dec(v_userName_972_);
lean_dec(v_fvarId_971_);
lean_del_object(v___x_953_);
lean_dec(v_snd_951_);
lean_dec(v_fst_950_);
lean_del_object(v___x_948_);
lean_dec(v_fst_946_);
lean_del_object(v___x_944_);
lean_del_object(v___x_929_);
v_a_984_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_979_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_979_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
else
{
lean_object* v_fvarId_994_; lean_object* v_userName_995_; lean_object* v_type_996_; lean_object* v_value_997_; uint8_t v_nondep_998_; uint8_t v_kind_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1026_; 
v_fvarId_994_ = lean_ctor_get(v_val_942_, 1);
v_userName_995_ = lean_ctor_get(v_val_942_, 2);
v_type_996_ = lean_ctor_get(v_val_942_, 3);
v_value_997_ = lean_ctor_get(v_val_942_, 4);
v_nondep_998_ = lean_ctor_get_uint8(v_val_942_, sizeof(void*)*5);
v_kind_999_ = lean_ctor_get_uint8(v_val_942_, sizeof(void*)*5 + 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_val_942_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v_val_942_, 0);
lean_dec(v_unused_1027_);
v___x_1001_ = v_val_942_;
v_isShared_1002_ = v_isSharedCheck_1026_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_value_997_);
lean_inc(v_type_996_);
lean_inc(v_userName_995_);
lean_inc(v_fvarId_994_);
lean_dec(v_val_942_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1026_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_Meta_Sym_preprocessExpr(v_type_996_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_Lean_Meta_Sym_preprocessExpr(v_value_997_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
lean_inc(v_snd_951_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 4, v_a_1006_);
lean_ctor_set(v___x_1001_, 3, v_a_1004_);
lean_ctor_set(v___x_1001_, 0, v_snd_951_);
v___x_1008_ = v___x_1001_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_snd_951_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_fvarId_994_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_userName_995_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v_a_1004_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v_a_1006_);
lean_ctor_set_uint8(v_reuseFailAlloc_1009_, sizeof(void*)*5, v_nondep_998_);
lean_ctor_set_uint8(v_reuseFailAlloc_1009_, sizeof(void*)*5 + 1, v_kind_999_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
v_decl_956_ = v___x_1008_;
goto v___jp_955_;
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_a_1004_);
lean_del_object(v___x_1001_);
lean_dec(v_userName_995_);
lean_dec(v_fvarId_994_);
lean_del_object(v___x_953_);
lean_dec(v_snd_951_);
lean_dec(v_fst_950_);
lean_del_object(v___x_948_);
lean_dec(v_fst_946_);
lean_del_object(v___x_944_);
lean_del_object(v___x_929_);
v_a_1010_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1005_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1005_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_del_object(v___x_1001_);
lean_dec_ref(v_value_997_);
lean_dec(v_userName_995_);
lean_dec(v_fvarId_994_);
lean_del_object(v___x_953_);
lean_dec(v_snd_951_);
lean_dec(v_fst_950_);
lean_del_object(v___x_948_);
lean_dec(v_fst_946_);
lean_del_object(v___x_944_);
lean_del_object(v___x_929_);
v_a_1018_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1003_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1003_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
v___jp_955_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_957_ = lean_unsigned_to_nat(1u);
v___x_958_ = lean_nat_add(v_snd_951_, v___x_957_);
lean_dec(v_snd_951_);
lean_inc_ref(v_decl_956_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v_decl_956_);
v___x_960_ = v___x_944_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_decl_956_);
v___x_960_ = v_reuseFailAlloc_970_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_961_ = l_Lean_PersistentArray_push___redArg(v_fst_950_, v___x_960_);
v___x_962_ = l_Lean_LocalDecl_fvarId(v_decl_956_);
v___x_963_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_946_, v___x_962_, v_decl_956_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v___x_958_);
lean_ctor_set(v___x_953_, 0, v___x_961_);
v___x_965_ = v___x_953_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_958_);
v___x_965_ = v_reuseFailAlloc_969_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_967_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_965_);
lean_ctor_set(v___x_948_, 0, v___x_963_);
v___x_967_ = v___x_948_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
v_a_933_ = v___x_967_;
goto v___jp_932_;
}
}
}
}
}
}
}
}
v___jp_932_:
{
lean_object* v___x_935_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v_a_933_);
lean_ctor_set(v___x_929_, 0, v___x_931_);
v___x_935_ = v___x_929_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_a_933_);
v___x_935_ = v_reuseFailAlloc_939_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
size_t v___x_936_; size_t v___x_937_; lean_object* v___x_938_; 
v___x_936_ = ((size_t)1ULL);
v___x_937_ = lean_usize_add(v_i_916_, v___x_936_);
v___x_938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_914_, v_sz_915_, v___x_937_, v___x_935_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3___boxed(lean_object* v_as_1034_, lean_object* v_sz_1035_, lean_object* v_i_1036_, lean_object* v_b_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
size_t v_sz_boxed_1045_; size_t v_i_boxed_1046_; lean_object* v_res_1047_; 
v_sz_boxed_1045_ = lean_unbox_usize(v_sz_1035_);
lean_dec(v_sz_1035_);
v_i_boxed_1046_ = lean_unbox_usize(v_i_1036_);
lean_dec(v_i_1036_);
v_res_1047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_as_1034_, v_sz_boxed_1045_, v_i_boxed_1046_, v_b_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec_ref(v_as_1034_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(lean_object* v_t_1048_, lean_object* v_init_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_root_1057_; lean_object* v_tail_1058_; lean_object* v___x_1059_; 
v_root_1057_ = lean_ctor_get(v_t_1048_, 0);
v_tail_1058_ = lean_ctor_get(v_t_1048_, 1);
lean_inc_ref(v_init_1049_);
v___x_1059_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_1049_, v_root_1057_, v_init_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec_ref(v_init_1049_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1096_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1096_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1096_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
if (lean_obj_tag(v_a_1060_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; 
v_a_1064_ = lean_ctor_get(v_a_1060_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v_a_1060_, 1);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v_a_1064_);
v___x_1066_ = v___x_1062_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; size_t v_sz_1071_; size_t v___x_1072_; lean_object* v___x_1073_; 
lean_del_object(v___x_1062_);
v_a_1068_ = lean_ctor_get(v_a_1060_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v_a_1060_, 1);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v_a_1068_);
v_sz_1071_ = lean_array_size(v_tail_1058_);
v___x_1072_ = ((size_t)0ULL);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_tail_1058_, v_sz_1071_, v___x_1072_, v___x_1070_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1087_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1087_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1087_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v_fst_1078_; 
v_fst_1078_ = lean_ctor_get(v_a_1074_, 0);
if (lean_obj_tag(v_fst_1078_) == 0)
{
lean_object* v_snd_1079_; lean_object* v___x_1081_; 
v_snd_1079_ = lean_ctor_get(v_a_1074_, 1);
lean_inc(v_snd_1079_);
lean_dec(v_a_1074_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v_snd_1079_);
v___x_1081_ = v___x_1076_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_snd_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
else
{
lean_object* v_val_1083_; lean_object* v___x_1085_; 
lean_inc_ref(v_fst_1078_);
lean_dec(v_a_1074_);
v_val_1083_ = lean_ctor_get(v_fst_1078_, 0);
lean_inc(v_val_1083_);
lean_dec_ref_known(v_fst_1078_, 1);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v_val_1083_);
v___x_1085_ = v___x_1076_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_val_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v_a_1088_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1073_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1073_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
v_a_1097_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1059_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1059_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1___boxed(lean_object* v_t_1105_, lean_object* v_init_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_t_1105_, v_init_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec_ref(v_t_1105_);
return v_res_1114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0(void){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1115_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1(void){
_start:
{
lean_object* v___x_1116_; lean_object* v_fvarIdToDecl_1117_; 
v___x_1116_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0);
v_fvarIdToDecl_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fvarIdToDecl_1117_, 0, v___x_1116_);
return v_fvarIdToDecl_1117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_unsigned_to_nat(32u);
v___x_1119_ = lean_mk_empty_array_with_capacity(v___x_1118_);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3(void){
_start:
{
size_t v___x_1121_; lean_object* v_index_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v_decls_1126_; 
v___x_1121_ = ((size_t)5ULL);
v_index_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = lean_unsigned_to_nat(32u);
v___x_1124_ = lean_mk_empty_array_with_capacity(v___x_1123_);
v___x_1125_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2);
v_decls_1126_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_decls_1126_, 0, v___x_1125_);
lean_ctor_set(v_decls_1126_, 1, v___x_1124_);
lean_ctor_set(v_decls_1126_, 2, v_index_1122_);
lean_ctor_set(v_decls_1126_, 3, v_index_1122_);
lean_ctor_set_usize(v_decls_1126_, 4, v___x_1121_);
return v_decls_1126_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4(void){
_start:
{
lean_object* v_index_1127_; lean_object* v_decls_1128_; lean_object* v___x_1129_; 
v_index_1127_ = lean_unsigned_to_nat(0u);
v_decls_1128_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v_decls_1128_);
lean_ctor_set(v___x_1129_, 1, v_index_1127_);
return v___x_1129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5(void){
_start:
{
lean_object* v___x_1130_; lean_object* v_fvarIdToDecl_1131_; lean_object* v___x_1132_; 
v___x_1130_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4);
v_fvarIdToDecl_1131_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v_fvarIdToDecl_1131_);
lean_ctor_set(v___x_1132_, 1, v___x_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(lean_object* v_lctx_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_decls_1141_; lean_object* v_auxDeclToFullName_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1170_; 
v_decls_1141_ = lean_ctor_get(v_lctx_1133_, 1);
v_auxDeclToFullName_1142_ = lean_ctor_get(v_lctx_1133_, 2);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_lctx_1133_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; 
v_unused_1171_ = lean_ctor_get(v_lctx_1133_, 0);
lean_dec(v_unused_1171_);
v___x_1144_ = v_lctx_1133_;
v_isShared_1145_ = v_isSharedCheck_1170_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_auxDeclToFullName_1142_);
lean_inc(v_decls_1141_);
lean_dec(v_lctx_1133_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1170_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5);
v___x_1147_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_decls_1141_, v___x_1146_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec_ref(v_decls_1141_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1161_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1161_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1161_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_snd_1152_; lean_object* v_fst_1153_; lean_object* v_fst_1154_; lean_object* v___x_1156_; 
v_snd_1152_ = lean_ctor_get(v_a_1148_, 1);
lean_inc(v_snd_1152_);
v_fst_1153_ = lean_ctor_get(v_a_1148_, 0);
lean_inc(v_fst_1153_);
lean_dec(v_a_1148_);
v_fst_1154_ = lean_ctor_get(v_snd_1152_, 0);
lean_inc(v_fst_1154_);
lean_dec(v_snd_1152_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v_fst_1154_);
lean_ctor_set(v___x_1144_, 0, v_fst_1153_);
v___x_1156_ = v___x_1144_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_fst_1153_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_fst_1154_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_auxDeclToFullName_1142_);
v___x_1156_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1158_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1156_);
v___x_1158_ = v___x_1150_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_del_object(v___x_1144_);
lean_dec(v_auxDeclToFullName_1142_);
v_a_1162_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1147_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1147_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___boxed(lean_object* v_lctx_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0(lean_object* v_00_u03b2_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_x_1182_, v_x_1183_, v_x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(lean_object* v_00_u03b2_1186_, lean_object* v_x_1187_, size_t v_x_1188_, size_t v_x_1189_, lean_object* v_x_1190_, lean_object* v_x_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_1187_, v_x_1188_, v_x_1189_, v_x_1190_, v_x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_, lean_object* v_x_1198_){
_start:
{
size_t v_x_10702__boxed_1199_; size_t v_x_10703__boxed_1200_; lean_object* v_res_1201_; 
v_x_10702__boxed_1199_ = lean_unbox_usize(v_x_1195_);
lean_dec(v_x_1195_);
v_x_10703__boxed_1200_ = lean_unbox_usize(v_x_1196_);
lean_dec(v_x_1196_);
v_res_1201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(v_00_u03b2_1193_, v_x_1194_, v_x_10702__boxed_1199_, v_x_10703__boxed_1200_, v_x_1197_, v_x_1198_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1202_, lean_object* v_n_1203_, lean_object* v_k_1204_, lean_object* v_v_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v_n_1203_, v_k_1204_, v_v_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1207_, size_t v_depth_1208_, lean_object* v_keys_1209_, lean_object* v_vals_1210_, lean_object* v_heq_1211_, lean_object* v_i_1212_, lean_object* v_entries_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_1208_, v_keys_1209_, v_vals_1210_, v_i_1212_, v_entries_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1215_, lean_object* v_depth_1216_, lean_object* v_keys_1217_, lean_object* v_vals_1218_, lean_object* v_heq_1219_, lean_object* v_i_1220_, lean_object* v_entries_1221_){
_start:
{
size_t v_depth_boxed_1222_; lean_object* v_res_1223_; 
v_depth_boxed_1222_ = lean_unbox_usize(v_depth_1216_);
lean_dec(v_depth_1216_);
v_res_1223_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(v_00_u03b2_1215_, v_depth_boxed_1222_, v_keys_1217_, v_vals_1218_, v_heq_1219_, v_i_1220_, v_entries_1221_);
lean_dec_ref(v_vals_1218_);
lean_dec_ref(v_keys_1217_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1224_, lean_object* v_x_1225_, lean_object* v_x_1226_, lean_object* v_x_1227_, lean_object* v_x_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1225_, v_x_1226_, v_x_1227_, v_x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1230_, lean_object* v_x_1231_, lean_object* v_x_1232_, lean_object* v_x_1233_){
_start:
{
lean_object* v_ks_1234_; lean_object* v_vs_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1259_; 
v_ks_1234_ = lean_ctor_get(v_x_1230_, 0);
v_vs_1235_ = lean_ctor_get(v_x_1230_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_x_1230_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1237_ = v_x_1230_;
v_isShared_1238_ = v_isSharedCheck_1259_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_vs_1235_);
lean_inc(v_ks_1234_);
lean_dec(v_x_1230_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1259_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = lean_array_get_size(v_ks_1234_);
v___x_1240_ = lean_nat_dec_lt(v_x_1231_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
lean_dec(v_x_1231_);
v___x_1241_ = lean_array_push(v_ks_1234_, v_x_1232_);
v___x_1242_ = lean_array_push(v_vs_1235_, v_x_1233_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v___x_1242_);
lean_ctor_set(v___x_1237_, 0, v___x_1241_);
v___x_1244_ = v___x_1237_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
else
{
lean_object* v_k_x27_1246_; uint8_t v___x_1247_; 
v_k_x27_1246_ = lean_array_fget_borrowed(v_ks_1234_, v_x_1231_);
v___x_1247_ = l_Lean_instBEqMVarId_beq(v_x_1232_, v_k_x27_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1249_; 
if (v_isShared_1238_ == 0)
{
v___x_1249_ = v___x_1237_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_ks_1234_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_vs_1235_);
v___x_1249_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_add(v_x_1231_, v___x_1250_);
lean_dec(v_x_1231_);
v_x_1230_ = v___x_1249_;
v_x_1231_ = v___x_1251_;
goto _start;
}
}
else
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1254_ = lean_array_fset(v_ks_1234_, v_x_1231_, v_x_1232_);
v___x_1255_ = lean_array_fset(v_vs_1235_, v_x_1231_, v_x_1233_);
lean_dec(v_x_1231_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v___x_1255_);
lean_ctor_set(v___x_1237_, 0, v___x_1254_);
v___x_1257_ = v___x_1237_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1260_, lean_object* v_k_1261_, lean_object* v_v_1262_){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1260_, v___x_1263_, v_k_1261_, v_v_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1265_, size_t v_x_1266_, size_t v_x_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_){
_start:
{
if (lean_obj_tag(v_x_1265_) == 0)
{
lean_object* v_es_1270_; size_t v___x_1271_; size_t v___x_1272_; lean_object* v_j_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_es_1270_ = lean_ctor_get(v_x_1265_, 0);
v___x_1271_ = ((size_t)31ULL);
v___x_1272_ = lean_usize_land(v_x_1266_, v___x_1271_);
v_j_1273_ = lean_usize_to_nat(v___x_1272_);
v___x_1274_ = lean_array_get_size(v_es_1270_);
v___x_1275_ = lean_nat_dec_lt(v_j_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_dec(v_j_1273_);
lean_dec(v_x_1269_);
lean_dec(v_x_1268_);
return v_x_1265_;
}
else
{
lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1314_; 
lean_inc_ref(v_es_1270_);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_x_1265_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v_x_1265_, 0);
lean_dec(v_unused_1315_);
v___x_1277_ = v_x_1265_;
v_isShared_1278_ = v_isSharedCheck_1314_;
goto v_resetjp_1276_;
}
else
{
lean_dec(v_x_1265_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1314_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_v_1279_; lean_object* v___x_1280_; lean_object* v_xs_x27_1281_; lean_object* v___y_1283_; 
v_v_1279_ = lean_array_fget(v_es_1270_, v_j_1273_);
v___x_1280_ = lean_box(0);
v_xs_x27_1281_ = lean_array_fset(v_es_1270_, v_j_1273_, v___x_1280_);
switch(lean_obj_tag(v_v_1279_))
{
case 0:
{
lean_object* v_key_1288_; lean_object* v_val_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1299_; 
v_key_1288_ = lean_ctor_get(v_v_1279_, 0);
v_val_1289_ = lean_ctor_get(v_v_1279_, 1);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_v_1279_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1291_ = v_v_1279_;
v_isShared_1292_ = v_isSharedCheck_1299_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_val_1289_);
lean_inc(v_key_1288_);
lean_dec(v_v_1279_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1299_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Lean_instBEqMVarId_beq(v_x_1268_, v_key_1288_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_del_object(v___x_1291_);
v___x_1294_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1288_, v_val_1289_, v_x_1268_, v_x_1269_);
v___x_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
v___y_1283_ = v___x_1295_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1297_; 
lean_dec(v_val_1289_);
lean_dec(v_key_1288_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 1, v_x_1269_);
lean_ctor_set(v___x_1291_, 0, v_x_1268_);
v___x_1297_ = v___x_1291_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_x_1268_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_x_1269_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
v___y_1283_ = v___x_1297_;
goto v___jp_1282_;
}
}
}
}
case 1:
{
lean_object* v_node_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1312_; 
v_node_1300_ = lean_ctor_get(v_v_1279_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_v_1279_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1302_ = v_v_1279_;
v_isShared_1303_ = v_isSharedCheck_1312_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_node_1300_);
lean_dec(v_v_1279_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1312_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
size_t v___x_1304_; size_t v___x_1305_; size_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1304_ = ((size_t)5ULL);
v___x_1305_ = lean_usize_shift_right(v_x_1266_, v___x_1304_);
v___x_1306_ = ((size_t)1ULL);
v___x_1307_ = lean_usize_add(v_x_1267_, v___x_1306_);
v___x_1308_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_node_1300_, v___x_1305_, v___x_1307_, v_x_1268_, v_x_1269_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1308_);
v___x_1310_ = v___x_1302_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
v___y_1283_ = v___x_1310_;
goto v___jp_1282_;
}
}
}
default: 
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_x_1268_);
lean_ctor_set(v___x_1313_, 1, v_x_1269_);
v___y_1283_ = v___x_1313_;
goto v___jp_1282_;
}
}
v___jp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = lean_array_fset(v_xs_x27_1281_, v_j_1273_, v___y_1283_);
lean_dec(v_j_1273_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1284_);
v___x_1286_ = v___x_1277_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
else
{
lean_object* v_ks_1316_; lean_object* v_vs_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1335_; 
v_ks_1316_ = lean_ctor_get(v_x_1265_, 0);
v_vs_1317_ = lean_ctor_get(v_x_1265_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1265_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1319_ = v_x_1265_;
v_isShared_1320_ = v_isSharedCheck_1335_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_vs_1317_);
lean_inc(v_ks_1316_);
lean_dec(v_x_1265_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1335_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_ks_1316_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_vs_1317_);
v___x_1322_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v_newNode_1323_; size_t v___x_1324_; uint8_t v___x_1325_; 
v_newNode_1323_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1322_, v_x_1268_, v_x_1269_);
v___x_1324_ = ((size_t)7ULL);
v___x_1325_ = lean_usize_dec_le(v___x_1324_, v_x_1267_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1326_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1323_);
v___x_1327_ = lean_unsigned_to_nat(4u);
v___x_1328_ = lean_nat_dec_lt(v___x_1326_, v___x_1327_);
lean_dec(v___x_1326_);
if (v___x_1328_ == 0)
{
lean_object* v_ks_1329_; lean_object* v_vs_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v_ks_1329_ = lean_ctor_get(v_newNode_1323_, 0);
lean_inc_ref(v_ks_1329_);
v_vs_1330_ = lean_ctor_get(v_newNode_1323_, 1);
lean_inc_ref(v_vs_1330_);
lean_dec_ref(v_newNode_1323_);
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0);
v___x_1333_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1267_, v_ks_1329_, v_vs_1330_, v___x_1331_, v___x_1332_);
lean_dec_ref(v_vs_1330_);
lean_dec_ref(v_ks_1329_);
return v___x_1333_;
}
else
{
return v_newNode_1323_;
}
}
else
{
return v_newNode_1323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1336_, lean_object* v_keys_1337_, lean_object* v_vals_1338_, lean_object* v_i_1339_, lean_object* v_entries_1340_){
_start:
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = lean_array_get_size(v_keys_1337_);
v___x_1342_ = lean_nat_dec_lt(v_i_1339_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_dec(v_i_1339_);
return v_entries_1340_;
}
else
{
lean_object* v_k_1343_; lean_object* v_v_1344_; uint64_t v___x_1345_; size_t v_h_1346_; size_t v___x_1347_; lean_object* v___x_1348_; size_t v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; size_t v_h_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_k_1343_ = lean_array_fget_borrowed(v_keys_1337_, v_i_1339_);
v_v_1344_ = lean_array_fget_borrowed(v_vals_1338_, v_i_1339_);
v___x_1345_ = l_Lean_instHashableMVarId_hash(v_k_1343_);
v_h_1346_ = lean_uint64_to_usize(v___x_1345_);
v___x_1347_ = ((size_t)5ULL);
v___x_1348_ = lean_unsigned_to_nat(1u);
v___x_1349_ = ((size_t)1ULL);
v___x_1350_ = lean_usize_sub(v_depth_1336_, v___x_1349_);
v___x_1351_ = lean_usize_mul(v___x_1347_, v___x_1350_);
v_h_1352_ = lean_usize_shift_right(v_h_1346_, v___x_1351_);
v___x_1353_ = lean_nat_add(v_i_1339_, v___x_1348_);
lean_dec(v_i_1339_);
lean_inc(v_v_1344_);
lean_inc(v_k_1343_);
v___x_1354_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_entries_1340_, v_h_1352_, v_depth_1336_, v_k_1343_, v_v_1344_);
v_i_1339_ = v___x_1353_;
v_entries_1340_ = v___x_1354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1356_, lean_object* v_keys_1357_, lean_object* v_vals_1358_, lean_object* v_i_1359_, lean_object* v_entries_1360_){
_start:
{
size_t v_depth_boxed_1361_; lean_object* v_res_1362_; 
v_depth_boxed_1361_ = lean_unbox_usize(v_depth_1356_);
lean_dec(v_depth_1356_);
v_res_1362_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1361_, v_keys_1357_, v_vals_1358_, v_i_1359_, v_entries_1360_);
lean_dec_ref(v_vals_1358_);
lean_dec_ref(v_keys_1357_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_){
_start:
{
size_t v_x_2259__boxed_1368_; size_t v_x_2260__boxed_1369_; lean_object* v_res_1370_; 
v_x_2259__boxed_1368_ = lean_unbox_usize(v_x_1364_);
lean_dec(v_x_1364_);
v_x_2260__boxed_1369_ = lean_unbox_usize(v_x_1365_);
lean_dec(v_x_1365_);
v_res_1370_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1363_, v_x_2259__boxed_1368_, v_x_2260__boxed_1369_, v_x_1366_, v_x_1367_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(lean_object* v_x_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_){
_start:
{
uint64_t v___x_1374_; size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1374_ = l_Lean_instHashableMVarId_hash(v_x_1372_);
v___x_1375_ = lean_uint64_to_usize(v___x_1374_);
v___x_1376_ = ((size_t)1ULL);
v___x_1377_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1371_, v___x_1375_, v___x_1376_, v_x_1372_, v_x_1373_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(lean_object* v_mvarId_1378_, lean_object* v_val_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1382_; lean_object* v_mctx_1383_; lean_object* v_cache_1384_; lean_object* v_zetaDeltaFVarIds_1385_; lean_object* v_postponed_1386_; lean_object* v_diag_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1416_; 
v___x_1382_ = lean_st_ref_take(v___y_1380_);
v_mctx_1383_ = lean_ctor_get(v___x_1382_, 0);
v_cache_1384_ = lean_ctor_get(v___x_1382_, 1);
v_zetaDeltaFVarIds_1385_ = lean_ctor_get(v___x_1382_, 2);
v_postponed_1386_ = lean_ctor_get(v___x_1382_, 3);
v_diag_1387_ = lean_ctor_get(v___x_1382_, 4);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1389_ = v___x_1382_;
v_isShared_1390_ = v_isSharedCheck_1416_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_diag_1387_);
lean_inc(v_postponed_1386_);
lean_inc(v_zetaDeltaFVarIds_1385_);
lean_inc(v_cache_1384_);
lean_inc(v_mctx_1383_);
lean_dec(v___x_1382_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1416_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_depth_1391_; lean_object* v_levelAssignDepth_1392_; lean_object* v_lmvarCounter_1393_; lean_object* v_mvarCounter_1394_; lean_object* v_lDecls_1395_; lean_object* v_decls_1396_; lean_object* v_userNames_1397_; lean_object* v_lAssignment_1398_; lean_object* v_eAssignment_1399_; lean_object* v_dAssignment_1400_; lean_object* v_instanceTypedMVars_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1415_; 
v_depth_1391_ = lean_ctor_get(v_mctx_1383_, 0);
v_levelAssignDepth_1392_ = lean_ctor_get(v_mctx_1383_, 1);
v_lmvarCounter_1393_ = lean_ctor_get(v_mctx_1383_, 2);
v_mvarCounter_1394_ = lean_ctor_get(v_mctx_1383_, 3);
v_lDecls_1395_ = lean_ctor_get(v_mctx_1383_, 4);
v_decls_1396_ = lean_ctor_get(v_mctx_1383_, 5);
v_userNames_1397_ = lean_ctor_get(v_mctx_1383_, 6);
v_lAssignment_1398_ = lean_ctor_get(v_mctx_1383_, 7);
v_eAssignment_1399_ = lean_ctor_get(v_mctx_1383_, 8);
v_dAssignment_1400_ = lean_ctor_get(v_mctx_1383_, 9);
v_instanceTypedMVars_1401_ = lean_ctor_get(v_mctx_1383_, 10);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_mctx_1383_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1403_ = v_mctx_1383_;
v_isShared_1404_ = v_isSharedCheck_1415_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_instanceTypedMVars_1401_);
lean_inc(v_dAssignment_1400_);
lean_inc(v_eAssignment_1399_);
lean_inc(v_lAssignment_1398_);
lean_inc(v_userNames_1397_);
lean_inc(v_decls_1396_);
lean_inc(v_lDecls_1395_);
lean_inc(v_mvarCounter_1394_);
lean_inc(v_lmvarCounter_1393_);
lean_inc(v_levelAssignDepth_1392_);
lean_inc(v_depth_1391_);
lean_dec(v_mctx_1383_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1415_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1405_ = lean_box(0);
v___x_1406_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_eAssignment_1399_, v_mvarId_1378_, v_val_1379_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 8, v___x_1406_);
v___x_1408_ = v___x_1403_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_depth_1391_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_levelAssignDepth_1392_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_lmvarCounter_1393_);
lean_ctor_set(v_reuseFailAlloc_1414_, 3, v_mvarCounter_1394_);
lean_ctor_set(v_reuseFailAlloc_1414_, 4, v_lDecls_1395_);
lean_ctor_set(v_reuseFailAlloc_1414_, 5, v_decls_1396_);
lean_ctor_set(v_reuseFailAlloc_1414_, 6, v_userNames_1397_);
lean_ctor_set(v_reuseFailAlloc_1414_, 7, v_lAssignment_1398_);
lean_ctor_set(v_reuseFailAlloc_1414_, 8, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1414_, 9, v_dAssignment_1400_);
lean_ctor_set(v_reuseFailAlloc_1414_, 10, v_instanceTypedMVars_1401_);
v___x_1408_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1410_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1408_);
v___x_1410_ = v___x_1389_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_cache_1384_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_zetaDeltaFVarIds_1385_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v_postponed_1386_);
lean_ctor_set(v_reuseFailAlloc_1413_, 4, v_diag_1387_);
v___x_1410_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_st_ref_put(v___y_1380_, v___x_1410_);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1405_);
return v___x_1412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg___boxed(lean_object* v_mvarId_1417_, lean_object* v_val_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1417_, v_val_1418_, v___y_1419_);
lean_dec(v___y_1419_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object* v_mvarId_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v___x_1430_; 
lean_inc(v_mvarId_1422_);
v___x_1430_ = l_Lean_MVarId_getDecl(v_mvarId_1422_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v_userName_1432_; lean_object* v_lctx_1433_; lean_object* v_type_1434_; lean_object* v_localInstances_1435_; lean_object* v___x_1436_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v_userName_1432_ = lean_ctor_get(v_a_1431_, 0);
lean_inc(v_userName_1432_);
v_lctx_1433_ = lean_ctor_get(v_a_1431_, 1);
lean_inc_ref(v_lctx_1433_);
v_type_1434_ = lean_ctor_get(v_a_1431_, 2);
lean_inc_ref(v_type_1434_);
v_localInstances_1435_ = lean_ctor_get(v_a_1431_, 4);
lean_inc_ref(v_localInstances_1435_);
lean_dec(v_a_1431_);
v___x_1436_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_1433_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1438_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1437_);
lean_dec_ref_known(v___x_1436_, 1);
v___x_1438_ = l_Lean_Meta_Sym_preprocessExpr(v_type_1434_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; uint8_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1438_, 1);
v___x_1440_ = 2;
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_1437_, v_localInstances_1435_, v_a_1439_, v___x_1440_, v_userName_1432_, v___x_1441_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1452_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc_n(v_a_1443_, 2);
lean_dec_ref_known(v___x_1442_, 1);
v___x_1444_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1422_, v_a_1443_, v_a_1426_);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v___x_1444_, 0);
lean_dec(v_unused_1453_);
v___x_1446_ = v___x_1444_;
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
else
{
lean_dec(v___x_1444_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1448_ = l_Lean_Expr_mvarId_x21(v_a_1443_);
lean_dec(v_a_1443_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1448_);
v___x_1450_ = v___x_1446_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_mvarId_1422_);
v_a_1454_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1442_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1442_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec(v_a_1437_);
lean_dec_ref(v_localInstances_1435_);
lean_dec(v_userName_1432_);
lean_dec(v_mvarId_1422_);
v_a_1462_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1438_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1438_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v_localInstances_1435_);
lean_dec_ref(v_type_1434_);
lean_dec(v_userName_1432_);
lean_dec(v_mvarId_1422_);
v_a_1470_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1436_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1436_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_mvarId_1422_);
v_a_1478_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1430_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1430_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar___boxed(lean_object* v_mvarId_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(lean_object* v_mvarId_1495_, lean_object* v_val_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1495_, v_val_1496_, v___y_1500_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___boxed(lean_object* v_mvarId_1505_, lean_object* v_val_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(v_mvarId_1505_, v_val_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0(lean_object* v_00_u03b2_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_x_1516_, v_x_1517_, v_x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1520_, lean_object* v_x_1521_, size_t v_x_1522_, size_t v_x_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1521_, v_x_1522_, v_x_1523_, v_x_1524_, v_x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
size_t v_x_2608__boxed_1533_; size_t v_x_2609__boxed_1534_; lean_object* v_res_1535_; 
v_x_2608__boxed_1533_ = lean_unbox_usize(v_x_1529_);
lean_dec(v_x_1529_);
v_x_2609__boxed_1534_ = lean_unbox_usize(v_x_1530_);
lean_dec(v_x_1530_);
v_res_1535_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(v_00_u03b2_1527_, v_x_1528_, v_x_2608__boxed_1533_, v_x_2609__boxed_1534_, v_x_1531_, v_x_1532_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1536_, lean_object* v_n_1537_, lean_object* v_k_1538_, lean_object* v_v_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1537_, v_k_1538_, v_v_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1541_, size_t v_depth_1542_, lean_object* v_keys_1543_, lean_object* v_vals_1544_, lean_object* v_heq_1545_, lean_object* v_i_1546_, lean_object* v_entries_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1542_, v_keys_1543_, v_vals_1544_, v_i_1546_, v_entries_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1549_, lean_object* v_depth_1550_, lean_object* v_keys_1551_, lean_object* v_vals_1552_, lean_object* v_heq_1553_, lean_object* v_i_1554_, lean_object* v_entries_1555_){
_start:
{
size_t v_depth_boxed_1556_; lean_object* v_res_1557_; 
v_depth_boxed_1556_ = lean_unbox_usize(v_depth_1550_);
lean_dec(v_depth_1550_);
v_res_1557_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1549_, v_depth_boxed_1556_, v_keys_1551_, v_vals_1552_, v_heq_1553_, v_i_1554_, v_entries_1555_);
lean_dec_ref(v_vals_1552_);
lean_dec_ref(v_keys_1551_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1558_, lean_object* v_x_1559_, lean_object* v_x_1560_, lean_object* v_x_1561_, lean_object* v_x_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1559_, v_x_1560_, v_x_1561_, v_x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(lean_object* v_msgData_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1570_; lean_object* v_env_1571_; lean_object* v___x_1572_; lean_object* v_toCold_1573_; lean_object* v_mctx_1574_; lean_object* v_lctx_1575_; lean_object* v_options_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1570_ = lean_st_ref_get(v___y_1568_);
v_env_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc_ref(v_env_1571_);
lean_dec(v___x_1570_);
v___x_1572_ = lean_st_ref_get(v___y_1566_);
v_toCold_1573_ = lean_ctor_get(v___y_1567_, 0);
v_mctx_1574_ = lean_ctor_get(v___x_1572_, 0);
lean_inc_ref(v_mctx_1574_);
lean_dec(v___x_1572_);
v_lctx_1575_ = lean_ctor_get(v___y_1565_, 2);
v_options_1576_ = lean_ctor_get(v_toCold_1573_, 2);
lean_inc_ref(v_options_1576_);
lean_inc_ref(v_lctx_1575_);
v___x_1577_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1577_, 0, v_env_1571_);
lean_ctor_set(v___x_1577_, 1, v_mctx_1574_);
lean_ctor_set(v___x_1577_, 2, v_lctx_1575_);
lean_ctor_set(v___x_1577_, 3, v_options_1576_);
v___x_1578_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v_msgData_1564_);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0___boxed(lean_object* v_msgData_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msgData_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(lean_object* v_msg_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_ref_1593_; lean_object* v___x_1594_; lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1603_; 
v_ref_1593_ = lean_ctor_get(v___y_1590_, 2);
v___x_1594_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msg_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1603_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1603_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1601_; 
lean_inc(v_ref_1593_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v_ref_1593_);
lean_ctor_set(v___x_1599_, 1, v_a_1595_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set_tag(v___x_1597_, 1);
lean_ctor_set(v___x_1597_, 0, v___x_1599_);
v___x_1601_ = v___x_1597_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(lean_object* v_msg_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
return v_res_1610_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0));
v___x_1613_ = l_Lean_stringToMessageData(v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(lean_object* v_msg_1617_, lean_object* v_e_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v___y_1627_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2));
v___x_1635_ = lean_string_dec_eq(v_msg_1617_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1636_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3));
v___x_1637_ = lean_string_append(v___x_1636_, v_msg_1617_);
lean_dec_ref(v_msg_1617_);
v___x_1638_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4));
v___x_1639_ = lean_string_append(v___x_1637_, v___x_1638_);
v___y_1627_ = v___x_1639_;
goto v___jp_1626_;
}
else
{
v___y_1627_ = v_msg_1617_;
goto v___jp_1626_;
}
v___jp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1628_ = l_Lean_stringToMessageData(v___y_1627_);
v___x_1629_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = l_Lean_indentExpr(v_e_1618_);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v___x_1632_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_);
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(lean_object* v_msg_1640_, lean_object* v_e_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1640_, v_e_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_object* v_00_u03b1_1650_, lean_object* v_msg_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_1651_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(lean_object* v_00_u03b1_1660_, lean_object* v_msg_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(v_00_u03b1_1660_, v_msg_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1670_, lean_object* v_vals_1671_, lean_object* v_i_1672_, lean_object* v_k_1673_){
_start:
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = lean_array_get_size(v_keys_1670_);
v___x_1675_ = lean_nat_dec_lt(v_i_1672_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; 
lean_dec(v_i_1672_);
v___x_1676_ = lean_box(0);
return v___x_1676_;
}
else
{
lean_object* v_k_x27_1677_; uint8_t v___x_1678_; 
v_k_x27_1677_ = lean_array_fget_borrowed(v_keys_1670_, v_i_1672_);
v___x_1678_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_1673_, v_k_x27_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_unsigned_to_nat(1u);
v___x_1680_ = lean_nat_add(v_i_1672_, v___x_1679_);
lean_dec(v_i_1672_);
v_i_1672_ = v___x_1680_;
goto _start;
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_array_fget_borrowed(v_vals_1671_, v_i_1672_);
lean_dec(v_i_1672_);
lean_inc(v___x_1682_);
lean_inc(v_k_x27_1677_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v_k_x27_1677_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
return v___x_1684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1685_, lean_object* v_vals_1686_, lean_object* v_i_1687_, lean_object* v_k_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_1685_, v_vals_1686_, v_i_1687_, v_k_1688_);
lean_dec_ref(v_k_1688_);
lean_dec_ref(v_vals_1686_);
lean_dec_ref(v_keys_1685_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(lean_object* v_x_1690_, size_t v_x_1691_, lean_object* v_x_1692_){
_start:
{
if (lean_obj_tag(v_x_1690_) == 0)
{
lean_object* v_es_1693_; lean_object* v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; lean_object* v_j_1697_; lean_object* v___x_1698_; 
v_es_1693_ = lean_ctor_get(v_x_1690_, 0);
v___x_1694_ = lean_box(2);
v___x_1695_ = ((size_t)31ULL);
v___x_1696_ = lean_usize_land(v_x_1691_, v___x_1695_);
v_j_1697_ = lean_usize_to_nat(v___x_1696_);
v___x_1698_ = lean_array_get_borrowed(v___x_1694_, v_es_1693_, v_j_1697_);
lean_dec(v_j_1697_);
switch(lean_obj_tag(v___x_1698_))
{
case 0:
{
lean_object* v_key_1699_; lean_object* v_val_1700_; uint8_t v___x_1701_; 
v_key_1699_ = lean_ctor_get(v___x_1698_, 0);
v_val_1700_ = lean_ctor_get(v___x_1698_, 1);
v___x_1701_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_1692_, v_key_1699_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_box(0);
return v___x_1702_;
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_inc(v_val_1700_);
lean_inc(v_key_1699_);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v_key_1699_);
lean_ctor_set(v___x_1703_, 1, v_val_1700_);
v___x_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
return v___x_1704_;
}
}
case 1:
{
lean_object* v_node_1705_; size_t v___x_1706_; size_t v___x_1707_; 
v_node_1705_ = lean_ctor_get(v___x_1698_, 0);
v___x_1706_ = ((size_t)5ULL);
v___x_1707_ = lean_usize_shift_right(v_x_1691_, v___x_1706_);
v_x_1690_ = v_node_1705_;
v_x_1691_ = v___x_1707_;
goto _start;
}
default: 
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_box(0);
return v___x_1709_;
}
}
}
else
{
lean_object* v_ks_1710_; lean_object* v_vs_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_ks_1710_ = lean_ctor_get(v_x_1690_, 0);
v_vs_1711_ = lean_ctor_get(v_x_1690_, 1);
v___x_1712_ = lean_unsigned_to_nat(0u);
v___x_1713_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_ks_1710_, v_vs_1711_, v___x_1712_, v_x_1692_);
return v___x_1713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_1714_, lean_object* v_x_1715_, lean_object* v_x_1716_){
_start:
{
size_t v_x_7386__boxed_1717_; lean_object* v_res_1718_; 
v_x_7386__boxed_1717_ = lean_unbox_usize(v_x_1715_);
lean_dec(v_x_1715_);
v_res_1718_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_1714_, v_x_7386__boxed_1717_, v_x_1716_);
lean_dec_ref(v_x_1716_);
lean_dec_ref(v_x_1714_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(lean_object* v_x_1719_, lean_object* v_x_1720_){
_start:
{
uint64_t v___x_1721_; size_t v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_1720_);
v___x_1722_ = lean_uint64_to_usize(v___x_1721_);
v___x_1723_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_1719_, v___x_1722_, v_x_1720_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg___boxed(lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_1724_, v_x_1725_);
lean_dec_ref(v_x_1725_);
lean_dec_ref(v_x_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0(lean_object* v_msg_1727_, lean_object* v_e_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___y_1741_; lean_object* v___x_1750_; lean_object* v_share_1751_; lean_object* v___x_1752_; 
v___x_1750_ = lean_st_ref_get(v___y_1730_);
v_share_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc_ref(v_share_1751_);
lean_dec(v___x_1750_);
v___x_1752_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_share_1751_, v_e_1728_);
lean_dec_ref(v_share_1751_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v___x_1753_; 
v___x_1753_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1727_, v_e_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
v___y_1741_ = v___x_1753_;
goto v___jp_1740_;
}
else
{
lean_object* v_val_1754_; lean_object* v_fst_1755_; size_t v___x_1756_; size_t v___x_1757_; uint8_t v___x_1758_; 
v_val_1754_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_val_1754_);
lean_dec_ref_known(v___x_1752_, 1);
v_fst_1755_ = lean_ctor_get(v_val_1754_, 0);
lean_inc(v_fst_1755_);
lean_dec(v_val_1754_);
v___x_1756_ = lean_ptr_addr(v_fst_1755_);
lean_dec(v_fst_1755_);
v___x_1757_ = lean_ptr_addr(v_e_1728_);
v___x_1758_ = lean_usize_dec_eq(v___x_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; 
v___x_1759_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1727_, v_e_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
v___y_1741_ = v___x_1759_;
goto v___jp_1740_;
}
else
{
lean_dec_ref(v_e_1728_);
lean_dec_ref(v_msg_1727_);
goto v___jp_1736_;
}
}
v___jp_1736_:
{
uint8_t v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = 1;
v___x_1738_ = lean_box(v___x_1737_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
v___jp_1740_:
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
v_a_1742_ = lean_ctor_get(v___y_1741_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___y_1741_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___y_1741_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___y_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0___boxed(lean_object* v_msg_1760_, lean_object* v_e_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_Expr_checkMaxShared___lam__0(v_msg_1760_, v_e_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(lean_object* v_a_1770_, lean_object* v_x_1771_){
_start:
{
if (lean_obj_tag(v_x_1771_) == 0)
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_box(0);
return v___x_1772_;
}
else
{
lean_object* v_key_1773_; lean_object* v_value_1774_; lean_object* v_tail_1775_; uint8_t v___x_1776_; 
v_key_1773_ = lean_ctor_get(v_x_1771_, 0);
v_value_1774_ = lean_ctor_get(v_x_1771_, 1);
v_tail_1775_ = lean_ctor_get(v_x_1771_, 2);
v___x_1776_ = lean_expr_eqv(v_key_1773_, v_a_1770_);
if (v___x_1776_ == 0)
{
v_x_1771_ = v_tail_1775_;
goto _start;
}
else
{
lean_object* v___x_1778_; 
lean_inc(v_value_1774_);
v___x_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_value_1774_);
return v___x_1778_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_1779_, lean_object* v_x_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_1779_, v_x_1780_);
lean_dec(v_x_1780_);
lean_dec_ref(v_a_1779_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(lean_object* v_m_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_buckets_1784_; lean_object* v___x_1785_; uint64_t v___x_1786_; uint64_t v___x_1787_; uint64_t v___x_1788_; uint64_t v_fold_1789_; uint64_t v___x_1790_; uint64_t v___x_1791_; uint64_t v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; size_t v___x_1795_; size_t v___x_1796_; size_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_buckets_1784_ = lean_ctor_get(v_m_1782_, 1);
v___x_1785_ = lean_array_get_size(v_buckets_1784_);
v___x_1786_ = l_Lean_Expr_hash(v_a_1783_);
v___x_1787_ = 32ULL;
v___x_1788_ = lean_uint64_shift_right(v___x_1786_, v___x_1787_);
v_fold_1789_ = lean_uint64_xor(v___x_1786_, v___x_1788_);
v___x_1790_ = 16ULL;
v___x_1791_ = lean_uint64_shift_right(v_fold_1789_, v___x_1790_);
v___x_1792_ = lean_uint64_xor(v_fold_1789_, v___x_1791_);
v___x_1793_ = lean_uint64_to_usize(v___x_1792_);
v___x_1794_ = lean_usize_of_nat(v___x_1785_);
v___x_1795_ = ((size_t)1ULL);
v___x_1796_ = lean_usize_sub(v___x_1794_, v___x_1795_);
v___x_1797_ = lean_usize_land(v___x_1793_, v___x_1796_);
v___x_1798_ = lean_array_uget_borrowed(v_buckets_1784_, v___x_1797_);
v___x_1799_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_1783_, v___x_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(lean_object* v_m_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_1800_, v_a_1801_);
lean_dec_ref(v_a_1801_);
lean_dec_ref(v_m_1800_);
return v_res_1802_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(lean_object* v_a_1803_, lean_object* v_x_1804_){
_start:
{
if (lean_obj_tag(v_x_1804_) == 0)
{
uint8_t v___x_1805_; 
v___x_1805_ = 0;
return v___x_1805_;
}
else
{
lean_object* v_key_1806_; lean_object* v_tail_1807_; uint8_t v___x_1808_; 
v_key_1806_ = lean_ctor_get(v_x_1804_, 0);
v_tail_1807_ = lean_ctor_get(v_x_1804_, 2);
v___x_1808_ = lean_expr_eqv(v_key_1806_, v_a_1803_);
if (v___x_1808_ == 0)
{
v_x_1804_ = v_tail_1807_;
goto _start;
}
else
{
return v___x_1808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_a_1810_, lean_object* v_x_1811_){
_start:
{
uint8_t v_res_1812_; lean_object* v_r_1813_; 
v_res_1812_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_1810_, v_x_1811_);
lean_dec(v_x_1811_);
lean_dec_ref(v_a_1810_);
v_r_1813_ = lean_box(v_res_1812_);
return v_r_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(lean_object* v_a_1814_, lean_object* v_b_1815_, lean_object* v_x_1816_){
_start:
{
if (lean_obj_tag(v_x_1816_) == 0)
{
lean_dec(v_b_1815_);
lean_dec_ref(v_a_1814_);
return v_x_1816_;
}
else
{
lean_object* v_key_1817_; lean_object* v_value_1818_; lean_object* v_tail_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1831_; 
v_key_1817_ = lean_ctor_get(v_x_1816_, 0);
v_value_1818_ = lean_ctor_get(v_x_1816_, 1);
v_tail_1819_ = lean_ctor_get(v_x_1816_, 2);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_x_1816_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1821_ = v_x_1816_;
v_isShared_1822_ = v_isSharedCheck_1831_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_tail_1819_);
lean_inc(v_value_1818_);
lean_inc(v_key_1817_);
lean_dec(v_x_1816_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1831_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_expr_eqv(v_key_1817_, v_a_1814_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_1814_, v_b_1815_, v_tail_1819_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 2, v___x_1824_);
v___x_1826_ = v___x_1821_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_key_1817_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_value_1818_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
else
{
lean_object* v___x_1829_; 
lean_dec(v_value_1818_);
lean_dec(v_key_1817_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 1, v_b_1815_);
lean_ctor_set(v___x_1821_, 0, v_a_1814_);
v___x_1829_ = v___x_1821_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1814_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_b_1815_);
lean_ctor_set(v_reuseFailAlloc_1830_, 2, v_tail_1819_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(lean_object* v_x_1832_, lean_object* v_x_1833_){
_start:
{
if (lean_obj_tag(v_x_1833_) == 0)
{
return v_x_1832_;
}
else
{
lean_object* v_key_1834_; lean_object* v_value_1835_; lean_object* v_tail_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1859_; 
v_key_1834_ = lean_ctor_get(v_x_1833_, 0);
v_value_1835_ = lean_ctor_get(v_x_1833_, 1);
v_tail_1836_ = lean_ctor_get(v_x_1833_, 2);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_x_1833_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1838_ = v_x_1833_;
v_isShared_1839_ = v_isSharedCheck_1859_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_tail_1836_);
lean_inc(v_value_1835_);
lean_inc(v_key_1834_);
lean_dec(v_x_1833_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1859_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; uint64_t v___x_1841_; uint64_t v___x_1842_; uint64_t v___x_1843_; uint64_t v_fold_1844_; uint64_t v___x_1845_; uint64_t v___x_1846_; uint64_t v___x_1847_; size_t v___x_1848_; size_t v___x_1849_; size_t v___x_1850_; size_t v___x_1851_; size_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1840_ = lean_array_get_size(v_x_1832_);
v___x_1841_ = l_Lean_Expr_hash(v_key_1834_);
v___x_1842_ = 32ULL;
v___x_1843_ = lean_uint64_shift_right(v___x_1841_, v___x_1842_);
v_fold_1844_ = lean_uint64_xor(v___x_1841_, v___x_1843_);
v___x_1845_ = 16ULL;
v___x_1846_ = lean_uint64_shift_right(v_fold_1844_, v___x_1845_);
v___x_1847_ = lean_uint64_xor(v_fold_1844_, v___x_1846_);
v___x_1848_ = lean_uint64_to_usize(v___x_1847_);
v___x_1849_ = lean_usize_of_nat(v___x_1840_);
v___x_1850_ = ((size_t)1ULL);
v___x_1851_ = lean_usize_sub(v___x_1849_, v___x_1850_);
v___x_1852_ = lean_usize_land(v___x_1848_, v___x_1851_);
v___x_1853_ = lean_array_uget_borrowed(v_x_1832_, v___x_1852_);
lean_inc(v___x_1853_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 2, v___x_1853_);
v___x_1855_ = v___x_1838_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_key_1834_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_value_1835_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_array_uset(v_x_1832_, v___x_1852_, v___x_1855_);
v_x_1832_ = v___x_1856_;
v_x_1833_ = v_tail_1836_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(lean_object* v_i_1860_, lean_object* v_source_1861_, lean_object* v_target_1862_){
_start:
{
lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = lean_array_get_size(v_source_1861_);
v___x_1864_ = lean_nat_dec_lt(v_i_1860_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_dec_ref(v_source_1861_);
lean_dec(v_i_1860_);
return v_target_1862_;
}
else
{
lean_object* v_es_1865_; lean_object* v___x_1866_; lean_object* v_source_1867_; lean_object* v_target_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_es_1865_ = lean_array_fget(v_source_1861_, v_i_1860_);
v___x_1866_ = lean_box(0);
v_source_1867_ = lean_array_fset(v_source_1861_, v_i_1860_, v___x_1866_);
v_target_1868_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_target_1862_, v_es_1865_);
v___x_1869_ = lean_unsigned_to_nat(1u);
v___x_1870_ = lean_nat_add(v_i_1860_, v___x_1869_);
lean_dec(v_i_1860_);
v_i_1860_ = v___x_1870_;
v_source_1861_ = v_source_1867_;
v_target_1862_ = v_target_1868_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(lean_object* v_data_1872_){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v_nbuckets_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1873_ = lean_array_get_size(v_data_1872_);
v___x_1874_ = lean_unsigned_to_nat(2u);
v_nbuckets_1875_ = lean_nat_mul(v___x_1873_, v___x_1874_);
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = lean_box(0);
v___x_1878_ = lean_mk_array(v_nbuckets_1875_, v___x_1877_);
v___x_1879_ = lean_array_propagate_mark(v_data_1872_, v___x_1878_);
v___x_1880_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v___x_1876_, v_data_1872_, v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(lean_object* v_m_1881_, lean_object* v_a_1882_, lean_object* v_b_1883_){
_start:
{
lean_object* v_size_1884_; lean_object* v_buckets_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1928_; 
v_size_1884_ = lean_ctor_get(v_m_1881_, 0);
v_buckets_1885_ = lean_ctor_get(v_m_1881_, 1);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_m_1881_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1887_ = v_m_1881_;
v_isShared_1888_ = v_isSharedCheck_1928_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_buckets_1885_);
lean_inc(v_size_1884_);
lean_dec(v_m_1881_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1928_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; uint64_t v___x_1890_; uint64_t v___x_1891_; uint64_t v___x_1892_; uint64_t v_fold_1893_; uint64_t v___x_1894_; uint64_t v___x_1895_; uint64_t v___x_1896_; size_t v___x_1897_; size_t v___x_1898_; size_t v___x_1899_; size_t v___x_1900_; size_t v___x_1901_; lean_object* v_bkt_1902_; uint8_t v___x_1903_; 
v___x_1889_ = lean_array_get_size(v_buckets_1885_);
v___x_1890_ = l_Lean_Expr_hash(v_a_1882_);
v___x_1891_ = 32ULL;
v___x_1892_ = lean_uint64_shift_right(v___x_1890_, v___x_1891_);
v_fold_1893_ = lean_uint64_xor(v___x_1890_, v___x_1892_);
v___x_1894_ = 16ULL;
v___x_1895_ = lean_uint64_shift_right(v_fold_1893_, v___x_1894_);
v___x_1896_ = lean_uint64_xor(v_fold_1893_, v___x_1895_);
v___x_1897_ = lean_uint64_to_usize(v___x_1896_);
v___x_1898_ = lean_usize_of_nat(v___x_1889_);
v___x_1899_ = ((size_t)1ULL);
v___x_1900_ = lean_usize_sub(v___x_1898_, v___x_1899_);
v___x_1901_ = lean_usize_land(v___x_1897_, v___x_1900_);
v_bkt_1902_ = lean_array_uget_borrowed(v_buckets_1885_, v___x_1901_);
v___x_1903_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_1882_, v_bkt_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v_size_x27_1905_; lean_object* v___x_1906_; lean_object* v_buckets_x27_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1904_ = lean_unsigned_to_nat(1u);
v_size_x27_1905_ = lean_nat_add(v_size_1884_, v___x_1904_);
lean_dec(v_size_1884_);
lean_inc(v_bkt_1902_);
v___x_1906_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1906_, 0, v_a_1882_);
lean_ctor_set(v___x_1906_, 1, v_b_1883_);
lean_ctor_set(v___x_1906_, 2, v_bkt_1902_);
v_buckets_x27_1907_ = lean_array_uset(v_buckets_1885_, v___x_1901_, v___x_1906_);
v___x_1908_ = lean_unsigned_to_nat(4u);
v___x_1909_ = lean_nat_mul(v_size_x27_1905_, v___x_1908_);
v___x_1910_ = lean_unsigned_to_nat(3u);
v___x_1911_ = lean_nat_div(v___x_1909_, v___x_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_array_get_size(v_buckets_x27_1907_);
v___x_1913_ = lean_nat_dec_le(v___x_1911_, v___x_1912_);
lean_dec(v___x_1911_);
if (v___x_1913_ == 0)
{
lean_object* v_val_1914_; lean_object* v___x_1916_; 
v_val_1914_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_buckets_x27_1907_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v_val_1914_);
lean_ctor_set(v___x_1887_, 0, v_size_x27_1905_);
v___x_1916_ = v___x_1887_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_size_x27_1905_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_val_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
else
{
lean_object* v___x_1919_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v_buckets_x27_1907_);
lean_ctor_set(v___x_1887_, 0, v_size_x27_1905_);
v___x_1919_ = v___x_1887_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_size_x27_1905_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_buckets_x27_1907_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
else
{
lean_object* v___x_1921_; lean_object* v_buckets_x27_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
lean_inc(v_bkt_1902_);
v___x_1921_ = lean_box(0);
v_buckets_x27_1922_ = lean_array_uset(v_buckets_1885_, v___x_1901_, v___x_1921_);
v___x_1923_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_1882_, v_b_1883_, v_bkt_1902_);
v___x_1924_ = lean_array_uset(v_buckets_x27_1922_, v___x_1901_, v___x_1923_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v___x_1924_);
v___x_1926_ = v___x_1887_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_size_1884_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(lean_object* v_g_1929_, lean_object* v_e_1930_, lean_object* v_a_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_a_1940_; lean_object* v___y_1946_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = lean_st_ref_get(v_a_1931_);
v___x_1949_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v___x_1948_, v_e_1930_);
lean_dec(v___x_1948_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v___x_1950_; 
lean_inc_ref(v_g_1929_);
lean_inc(v___y_1937_);
lean_inc_ref(v___y_1936_);
lean_inc(v___y_1935_);
lean_inc_ref(v___y_1934_);
lean_inc(v___y_1933_);
lean_inc_ref(v___y_1932_);
lean_inc_ref(v_e_1930_);
v___x_1950_ = lean_apply_8(v_g_1929_, v_e_1930_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, lean_box(0));
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v_d_1953_; lean_object* v_b_1954_; lean_object* v___y_1955_; uint8_t v___x_1958_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1958_ = lean_unbox(v_a_1951_);
lean_dec(v_a_1951_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; 
lean_dec_ref(v_g_1929_);
v___x_1959_ = lean_box(0);
v_a_1940_ = v___x_1959_;
goto v___jp_1939_;
}
else
{
switch(lean_obj_tag(v_e_1930_))
{
case 7:
{
lean_object* v_binderType_1960_; lean_object* v_body_1961_; 
v_binderType_1960_ = lean_ctor_get(v_e_1930_, 1);
v_body_1961_ = lean_ctor_get(v_e_1930_, 2);
lean_inc_ref(v_body_1961_);
lean_inc_ref(v_binderType_1960_);
v_d_1953_ = v_binderType_1960_;
v_b_1954_ = v_body_1961_;
v___y_1955_ = v_a_1931_;
goto v___jp_1952_;
}
case 6:
{
lean_object* v_binderType_1962_; lean_object* v_body_1963_; 
v_binderType_1962_ = lean_ctor_get(v_e_1930_, 1);
v_body_1963_ = lean_ctor_get(v_e_1930_, 2);
lean_inc_ref(v_body_1963_);
lean_inc_ref(v_binderType_1962_);
v_d_1953_ = v_binderType_1962_;
v_b_1954_ = v_body_1963_;
v___y_1955_ = v_a_1931_;
goto v___jp_1952_;
}
case 8:
{
lean_object* v_type_1964_; lean_object* v_value_1965_; lean_object* v_body_1966_; lean_object* v___x_1967_; 
v_type_1964_ = lean_ctor_get(v_e_1930_, 1);
v_value_1965_ = lean_ctor_get(v_e_1930_, 2);
v_body_1966_ = lean_ctor_get(v_e_1930_, 3);
lean_inc_ref(v_type_1964_);
lean_inc_ref(v_g_1929_);
v___x_1967_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1929_, v_type_1964_, v_a_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v___x_1968_; 
lean_dec_ref_known(v___x_1967_, 1);
lean_inc_ref(v_value_1965_);
lean_inc_ref(v_g_1929_);
v___x_1968_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1929_, v_value_1965_, v_a_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v___x_1969_; 
lean_dec_ref_known(v___x_1968_, 1);
lean_inc_ref(v_body_1966_);
v___x_1969_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1929_, v_body_1966_, v_a_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
v___y_1946_ = v___x_1969_;
goto v___jp_1945_;
}
else
{
lean_dec_ref(v_g_1929_);
v___y_1946_ = v___x_1968_;
goto v___jp_1945_;
}
}
else
{
lean_dec_ref(v_g_1929_);
v___y_1946_ = v___x_1967_;
goto v___jp_1945_;
}
}
case 5:
{
lean_object* v_fn_1970_; lean_object* v_arg_1971_; lean_object* v___x_1972_; 
v_fn_1970_ = lean_ctor_get(v_e_1930_, 0);
v_arg_1971_ = lean_ctor_get(v_e_1930_, 1);
lean_inc_ref(v_fn_1970_);
lean_inc_ref(v_g_1929_);
v___x_1972_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1929_, v_fn_1970_, v_a_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v___x_1973_; 
lean_dec_ref_known(v___x_1972_, 1);
lean_inc_ref(v_arg_1971_);
v___x_1973_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1929_, v_arg_1971_, v_a_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
v___y_1946_ = v___x_1973_;
goto v___jp_1945_;
}
else
{
lean_dec_ref(v_g_1929_);
v___y_1946_ = v___x_1972_;
goto v___jp_1945_;
}
}
case 10:
{
lean_object* v_expr_1974_; lean_object* v___x_1975_; 
v_expr_1974_ = lean_ctor_get(v_e_1930_, 1);
lean_inc_ref(v_expr_1974_);
v___x_1975_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1929_, v_expr_1974_, v_a_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
v___y_1946_ = v___x_1975_;
goto v___jp_1945_;
}
case 11:
{
lean_object* v_struct_1976_; lean_object* v___x_1977_; 
v_struct_1976_ = lean_ctor_get(v_e_1930_, 2);
lean_inc_ref(v_struct_1976_);
v___x_1977_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1929_, v_struct_1976_, v_a_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
v___y_1946_ = v___x_1977_;
goto v___jp_1945_;
}
default: 
{
lean_object* v___x_1978_; 
lean_dec_ref(v_g_1929_);
v___x_1978_ = lean_box(0);
v_a_1940_ = v___x_1978_;
goto v___jp_1939_;
}
}
}
v___jp_1952_:
{
lean_object* v___x_1956_; 
lean_inc_ref(v_g_1929_);
v___x_1956_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1929_, v_d_1953_, v___y_1955_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v___x_1957_; 
lean_dec_ref_known(v___x_1956_, 1);
v___x_1957_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1929_, v_b_1954_, v___y_1955_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
v___y_1946_ = v___x_1957_;
goto v___jp_1945_;
}
else
{
lean_dec_ref(v_b_1954_);
lean_dec_ref(v_g_1929_);
v___y_1946_ = v___x_1956_;
goto v___jp_1945_;
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec_ref(v_e_1930_);
lean_dec_ref(v_g_1929_);
v_a_1979_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1950_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1950_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
else
{
lean_object* v_val_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec_ref(v_e_1930_);
lean_dec_ref(v_g_1929_);
v_val_1987_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1949_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_val_1987_);
lean_dec(v___x_1949_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set_tag(v___x_1989_, 0);
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_val_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
v___jp_1939_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1941_ = lean_st_ref_take(v_a_1931_);
v___x_1942_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v___x_1941_, v_e_1930_, v_a_1940_);
v___x_1943_ = lean_st_ref_put(v_a_1931_, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v_a_1940_);
return v___x_1944_;
}
v___jp_1945_:
{
if (lean_obj_tag(v___y_1946_) == 0)
{
lean_object* v_a_1947_; 
v_a_1947_ = lean_ctor_get(v___y_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___y_1946_, 1);
v_a_1940_ = v_a_1947_;
goto v___jp_1939_;
}
else
{
lean_dec_ref(v_e_1930_);
return v___y_1946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(lean_object* v_g_1995_, lean_object* v_e_1996_, lean_object* v_a_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1995_, v_e_1996_, v_a_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v_a_1997_);
return v_res_2005_;
}
}
static lean_object* _init_l_Lean_Expr_checkMaxShared___closed__0(void){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2006_ = lean_box(0);
v___x_2007_ = lean_unsigned_to_nat(16u);
v___x_2008_ = lean_mk_array(v___x_2007_, v___x_2006_);
return v___x_2008_;
}
}
static lean_object* _init_l_Lean_Expr_checkMaxShared___closed__1(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2009_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__0, &l_Lean_Expr_checkMaxShared___closed__0_once, _init_l_Lean_Expr_checkMaxShared___closed__0);
v___x_2010_ = lean_unsigned_to_nat(0u);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v___x_2009_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared(lean_object* v_e_2012_, lean_object* v_msg_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v___f_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___f_2021_ = lean_alloc_closure((void*)(l_Lean_Expr_checkMaxShared___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2021_, 0, v_msg_2013_);
v___x_2022_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__1, &l_Lean_Expr_checkMaxShared___closed__1_once, _init_l_Lean_Expr_checkMaxShared___closed__1);
v___x_2023_ = lean_st_mk_ref(v___x_2022_);
v___x_2024_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v___f_2021_, v_e_2012_, v___x_2023_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2033_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2033_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2033_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2029_ = lean_st_ref_get(v___x_2023_);
lean_dec(v___x_2023_);
lean_dec(v___x_2029_);
if (v_isShared_2028_ == 0)
{
v___x_2031_ = v___x_2027_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2025_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
else
{
lean_dec(v___x_2023_);
return v___x_2024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___boxed(lean_object* v_e_2034_, lean_object* v_msg_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_Expr_checkMaxShared(v_e_2034_, v_msg_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
lean_dec(v_a_2037_);
lean_dec_ref(v_a_2036_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(lean_object* v_00_u03b2_2044_, lean_object* v_x_2045_, lean_object* v_x_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_2045_, v_x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___boxed(lean_object* v_00_u03b2_2048_, lean_object* v_x_2049_, lean_object* v_x_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(v_00_u03b2_2048_, v_x_2049_, v_x_2050_);
lean_dec_ref(v_x_2050_);
lean_dec_ref(v_x_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_object* v_00_u03b2_2052_, lean_object* v_x_2053_, size_t v_x_2054_, lean_object* v_x_2055_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_2053_, v_x_2054_, v_x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2057_, lean_object* v_x_2058_, lean_object* v_x_2059_, lean_object* v_x_2060_){
_start:
{
size_t v_x_7973__boxed_2061_; lean_object* v_res_2062_; 
v_x_7973__boxed_2061_ = lean_unbox_usize(v_x_2059_);
lean_dec(v_x_2059_);
v_res_2062_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(v_00_u03b2_2057_, v_x_2058_, v_x_7973__boxed_2061_, v_x_2060_);
lean_dec_ref(v_x_2060_);
lean_dec_ref(v_x_2058_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(lean_object* v_00_u03b2_2063_, lean_object* v_m_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_2064_, v_a_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2067_, lean_object* v_m_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(v_00_u03b2_2067_, v_m_2068_, v_a_2069_);
lean_dec_ref(v_a_2069_);
lean_dec_ref(v_m_2068_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(lean_object* v_00_u03b2_2071_, lean_object* v_m_2072_, lean_object* v_a_2073_, lean_object* v_b_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_m_2072_, v_a_2073_, v_b_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2076_, lean_object* v_keys_2077_, lean_object* v_vals_2078_, lean_object* v_heq_2079_, lean_object* v_i_2080_, lean_object* v_k_2081_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_2077_, v_vals_2078_, v_i_2080_, v_k_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2083_, lean_object* v_keys_2084_, lean_object* v_vals_2085_, lean_object* v_heq_2086_, lean_object* v_i_2087_, lean_object* v_k_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(v_00_u03b2_2083_, v_keys_2084_, v_vals_2085_, v_heq_2086_, v_i_2087_, v_k_2088_);
lean_dec_ref(v_k_2088_);
lean_dec_ref(v_vals_2085_);
lean_dec_ref(v_keys_2084_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2090_, lean_object* v_a_2091_, lean_object* v_x_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_2091_, v_x_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2094_, lean_object* v_a_2095_, lean_object* v_x_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(v_00_u03b2_2094_, v_a_2095_, v_x_2096_);
lean_dec(v_x_2096_);
lean_dec_ref(v_a_2095_);
return v_res_2097_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2098_, lean_object* v_a_2099_, lean_object* v_x_2100_){
_start:
{
uint8_t v___x_2101_; 
v___x_2101_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_2099_, v_x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2102_, lean_object* v_a_2103_, lean_object* v_x_2104_){
_start:
{
uint8_t v_res_2105_; lean_object* v_r_2106_; 
v_res_2105_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(v_00_u03b2_2102_, v_a_2103_, v_x_2104_);
lean_dec(v_x_2104_);
lean_dec_ref(v_a_2103_);
v_r_2106_ = lean_box(v_res_2105_);
return v_r_2106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2107_, lean_object* v_data_2108_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_data_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2110_, lean_object* v_a_2111_, lean_object* v_b_2112_, lean_object* v_x_2113_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_2111_, v_b_2112_, v_x_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_2115_, lean_object* v_i_2116_, lean_object* v_source_2117_, lean_object* v_target_2118_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v_i_2116_, v_source_2117_, v_target_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9(lean_object* v_00_u03b2_2120_, lean_object* v_x_2121_, lean_object* v_x_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_x_2121_, v_x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared(lean_object* v_mvarId_2124_, lean_object* v_msg_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_MVarId_getDecl(v_mvarId_2124_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v_type_2135_; lean_object* v___x_2136_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
v_type_2135_ = lean_ctor_get(v_a_2134_, 2);
lean_inc_ref(v_type_2135_);
lean_dec(v_a_2134_);
v___x_2136_ = l_Lean_Expr_checkMaxShared(v_type_2135_, v_msg_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
return v___x_2136_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v_msg_2125_);
v_a_2137_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2133_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2133_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared___boxed(lean_object* v_mvarId_2145_, lean_object* v_msg_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_MVarId_checkMaxShared(v_mvarId_2145_, v_msg_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
return v_res_2154_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(lean_object* v_x_2155_){
_start:
{
if (lean_obj_tag(v_x_2155_) == 0)
{
uint8_t v___x_2156_; 
v___x_2156_ = 0;
return v___x_2156_;
}
else
{
lean_object* v_head_2157_; lean_object* v_tail_2158_; uint8_t v___x_2159_; 
v_head_2157_ = lean_ctor_get(v_x_2155_, 0);
v_tail_2158_ = lean_ctor_get(v_x_2155_, 1);
v___x_2159_ = l_Lean_Level_isAlreadyNormalizedCheap(v_head_2157_);
if (v___x_2159_ == 0)
{
uint8_t v___x_2160_; 
v___x_2160_ = 1;
return v___x_2160_;
}
else
{
v_x_2155_ = v_tail_2158_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0___boxed(lean_object* v_x_2162_){
_start:
{
uint8_t v_res_2163_; lean_object* v_r_2164_; 
v_res_2163_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_x_2162_);
lean_dec(v_x_2162_);
v_r_2164_ = lean_box(v_res_2163_);
return v_r_2164_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(lean_object* v_x_2165_){
_start:
{
switch(lean_obj_tag(v_x_2165_))
{
case 4:
{
lean_object* v_us_2166_; uint8_t v___x_2167_; 
v_us_2166_ = lean_ctor_get(v_x_2165_, 1);
v___x_2167_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_us_2166_);
return v___x_2167_;
}
case 3:
{
lean_object* v_u_2168_; uint8_t v___x_2169_; 
v_u_2168_ = lean_ctor_get(v_x_2165_, 0);
v___x_2169_ = l_Lean_Level_isAlreadyNormalizedCheap(v_u_2168_);
if (v___x_2169_ == 0)
{
uint8_t v___x_2170_; 
v___x_2170_ = 1;
return v___x_2170_;
}
else
{
uint8_t v___x_2171_; 
v___x_2171_ = 0;
return v___x_2171_;
}
}
default: 
{
uint8_t v___x_2172_; 
v___x_2172_ = 0;
return v___x_2172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(lean_object* v_x_2173_){
_start:
{
uint8_t v_res_2174_; lean_object* v_r_2175_; 
v_res_2174_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(v_x_2173_);
lean_dec_ref(v_x_2173_);
v_r_2175_ = lean_box(v_res_2174_);
return v_r_2175_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(lean_object* v_e_2177_){
_start:
{
lean_object* v___f_2178_; lean_object* v___x_2179_; 
v___f_2178_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0));
v___x_2179_ = lean_find_expr(v___f_2178_, v_e_2177_);
if (lean_obj_tag(v___x_2179_) == 0)
{
uint8_t v___x_2180_; 
v___x_2180_ = 1;
return v___x_2180_;
}
else
{
uint8_t v___x_2181_; 
lean_dec_ref_known(v___x_2179_, 1);
v___x_2181_ = 0;
return v___x_2181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___boxed(lean_object* v_e_2182_){
_start:
{
uint8_t v_res_2183_; lean_object* v_r_2184_; 
v_res_2183_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_2182_);
lean_dec_ref(v_e_2182_);
v_r_2184_ = lean_box(v_res_2183_);
return v_r_2184_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
if (lean_obj_tag(v_a_2185_) == 0)
{
lean_object* v___x_2187_; 
v___x_2187_ = l_List_reverse___redArg(v_a_2186_);
return v___x_2187_;
}
else
{
lean_object* v_head_2188_; lean_object* v_tail_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2198_; 
v_head_2188_ = lean_ctor_get(v_a_2185_, 0);
v_tail_2189_ = lean_ctor_get(v_a_2185_, 1);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_a_2185_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2191_ = v_a_2185_;
v_isShared_2192_ = v_isSharedCheck_2198_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_tail_2189_);
lean_inc(v_head_2188_);
lean_dec(v_a_2185_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2198_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2193_ = l_Lean_Level_normalize(v_head_2188_);
lean_dec(v_head_2188_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 1, v_a_2186_);
lean_ctor_set(v___x_2191_, 0, v___x_2193_);
v___x_2195_ = v___x_2191_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_a_2186_);
v___x_2195_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
v_a_2185_ = v_tail_2189_;
v_a_2186_ = v___x_2195_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0(lean_object* v_e_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___y_2206_; lean_object* v___y_2210_; 
switch(lean_obj_tag(v_e_2201_))
{
case 3:
{
lean_object* v_u_2213_; lean_object* v___x_2214_; size_t v___x_2215_; size_t v___x_2216_; uint8_t v___x_2217_; 
v_u_2213_ = lean_ctor_get(v_e_2201_, 0);
v___x_2214_ = l_Lean_Level_normalize(v_u_2213_);
v___x_2215_ = lean_ptr_addr(v_u_2213_);
v___x_2216_ = lean_ptr_addr(v___x_2214_);
v___x_2217_ = lean_usize_dec_eq(v___x_2215_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; 
lean_dec_ref_known(v_e_2201_, 1);
v___x_2218_ = l_Lean_Expr_sort___override(v___x_2214_);
v___y_2206_ = v___x_2218_;
goto v___jp_2205_;
}
else
{
lean_dec(v___x_2214_);
v___y_2206_ = v_e_2201_;
goto v___jp_2205_;
}
}
case 4:
{
lean_object* v_declName_2219_; lean_object* v_us_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v_declName_2219_ = lean_ctor_get(v_e_2201_, 0);
v_us_2220_ = lean_ctor_get(v_e_2201_, 1);
v___x_2221_ = lean_box(0);
lean_inc(v_us_2220_);
v___x_2222_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(v_us_2220_, v___x_2221_);
v___x_2223_ = l_ptrEqList___redArg(v_us_2220_, v___x_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; 
lean_inc(v_declName_2219_);
lean_dec_ref_known(v_e_2201_, 2);
v___x_2224_ = l_Lean_Expr_const___override(v_declName_2219_, v___x_2222_);
v___y_2210_ = v___x_2224_;
goto v___jp_2209_;
}
else
{
lean_dec(v___x_2222_);
v___y_2210_ = v_e_2201_;
goto v___jp_2209_;
}
}
default: 
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec_ref(v_e_2201_);
v___x_2225_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___lam__0___closed__0));
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
return v___x_2226_;
}
}
v___jp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___y_2206_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
v___jp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___y_2210_);
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed(lean_object* v_e_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Meta_Sym_normalizeLevels___lam__0(v_e_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1(lean_object* v_e_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v_e_2232_);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed(lean_object* v_e_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_Meta_Sym_normalizeLevels___lam__1(v_e_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
return v_res_2242_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = l_Lean_maxRecDepthErrorMessage;
v___x_2249_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
return v___x_2249_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3);
v___x_2251_ = l_Lean_MessageData_ofFormat(v___x_2250_);
return v___x_2251_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4);
v___x_2253_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__2));
v___x_2254_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
lean_ctor_set(v___x_2254_, 1, v___x_2252_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_ref_2255_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v_ref_2255_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_ref_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2260_);
return v_res_2262_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = lean_box(0);
v___x_2264_ = l_Lean_interruptExceptionId;
v___x_2265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v___x_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg(){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0);
v___x_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___boxed(lean_object* v___y_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(lean_object* v_x_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v___y_2277_; lean_object* v___y_2287_; uint16_t v___y_2288_; uint8_t v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; uint8_t v___y_2292_; lean_object* v_toCold_2297_; lean_object* v_currRecDepth_2298_; lean_object* v_ref_2299_; uint16_t v_optionFlags_2300_; uint8_t v_suppressElabErrors_2301_; uint8_t v_isRecordingDeps_2302_; lean_object* v_maxRecDepth_2303_; lean_object* v_cancelTk_x3f_2304_; 
v_toCold_2297_ = lean_ctor_get(v___y_2273_, 0);
v_currRecDepth_2298_ = lean_ctor_get(v___y_2273_, 1);
v_ref_2299_ = lean_ctor_get(v___y_2273_, 2);
v_optionFlags_2300_ = lean_ctor_get_uint16(v___y_2273_, sizeof(void*)*3);
v_suppressElabErrors_2301_ = lean_ctor_get_uint8(v___y_2273_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2302_ = lean_ctor_get_uint8(v___y_2273_, sizeof(void*)*3 + 3);
v_maxRecDepth_2303_ = lean_ctor_get(v_toCold_2297_, 3);
v_cancelTk_x3f_2304_ = lean_ctor_get(v_toCold_2297_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2304_) == 1)
{
lean_object* v_val_2310_; uint8_t v___x_2311_; 
v_val_2310_ = lean_ctor_get(v_cancelTk_x3f_2304_, 0);
v___x_2311_ = l_IO_CancelToken_isSet(v_val_2310_);
if (v___x_2311_ == 0)
{
goto v___jp_2305_;
}
else
{
lean_object* v___x_2312_; lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref(v_x_2271_);
v___x_2312_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
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
else
{
goto v___jp_2305_;
}
v___jp_2276_:
{
if (lean_obj_tag(v___y_2277_) == 0)
{
return v___y_2277_;
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
v_a_2278_ = lean_ctor_get(v___y_2277_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___y_2277_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___y_2277_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___y_2277_);
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
v___jp_2286_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2293_ = lean_unsigned_to_nat(1u);
v___x_2294_ = lean_nat_add(v___y_2287_, v___x_2293_);
lean_inc_ref(v___y_2291_);
v___x_2295_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2295_, 0, v___y_2291_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
lean_ctor_set(v___x_2295_, 2, v___y_2290_);
lean_ctor_set_uint16(v___x_2295_, sizeof(void*)*3, v___y_2288_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*3 + 2, v___y_2289_);
lean_ctor_set_uint8(v___x_2295_, sizeof(void*)*3 + 3, v___y_2292_);
lean_inc(v___y_2274_);
lean_inc(v___y_2272_);
v___x_2296_ = lean_apply_4(v_x_2271_, v___y_2272_, v___x_2295_, v___y_2274_, lean_box(0));
v___y_2277_ = v___x_2296_;
goto v___jp_2276_;
}
v___jp_2305_:
{
lean_object* v___x_2306_; uint8_t v___x_2307_; 
v___x_2306_ = lean_unsigned_to_nat(0u);
v___x_2307_ = lean_nat_dec_eq(v_maxRecDepth_2303_, v___x_2306_);
if (v___x_2307_ == 0)
{
uint8_t v___x_2308_; 
v___x_2308_ = lean_nat_dec_eq(v_currRecDepth_2298_, v_maxRecDepth_2303_);
if (v___x_2308_ == 0)
{
lean_inc(v_ref_2299_);
v___y_2287_ = v_currRecDepth_2298_;
v___y_2288_ = v_optionFlags_2300_;
v___y_2289_ = v_suppressElabErrors_2301_;
v___y_2290_ = v_ref_2299_;
v___y_2291_ = v_toCold_2297_;
v___y_2292_ = v_isRecordingDeps_2302_;
goto v___jp_2286_;
}
else
{
lean_object* v___x_2309_; 
lean_dec_ref(v_x_2271_);
lean_inc(v_ref_2299_);
v___x_2309_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2299_);
v___y_2277_ = v___x_2309_;
goto v___jp_2276_;
}
}
else
{
lean_inc(v_ref_2299_);
v___y_2287_ = v_currRecDepth_2298_;
v___y_2288_ = v_optionFlags_2300_;
v___y_2289_ = v_suppressElabErrors_2301_;
v___y_2290_ = v_ref_2299_;
v___y_2291_ = v_toCold_2297_;
v___y_2292_ = v_isRecordingDeps_2302_;
goto v___jp_2286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_x_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v_x_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(lean_object* v_x_2327_, lean_object* v_x_2328_){
_start:
{
if (lean_obj_tag(v_x_2328_) == 0)
{
return v_x_2327_;
}
else
{
lean_object* v_key_2329_; lean_object* v_value_2330_; lean_object* v_tail_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2354_; 
v_key_2329_ = lean_ctor_get(v_x_2328_, 0);
v_value_2330_ = lean_ctor_get(v_x_2328_, 1);
v_tail_2331_ = lean_ctor_get(v_x_2328_, 2);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_x_2328_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2333_ = v_x_2328_;
v_isShared_2334_ = v_isSharedCheck_2354_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_tail_2331_);
lean_inc(v_value_2330_);
lean_inc(v_key_2329_);
lean_dec(v_x_2328_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2354_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; uint64_t v___x_2336_; uint64_t v___x_2337_; uint64_t v___x_2338_; uint64_t v_fold_2339_; uint64_t v___x_2340_; uint64_t v___x_2341_; uint64_t v___x_2342_; size_t v___x_2343_; size_t v___x_2344_; size_t v___x_2345_; size_t v___x_2346_; size_t v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2335_ = lean_array_get_size(v_x_2327_);
v___x_2336_ = l_Lean_ExprStructEq_hash(v_key_2329_);
v___x_2337_ = 32ULL;
v___x_2338_ = lean_uint64_shift_right(v___x_2336_, v___x_2337_);
v_fold_2339_ = lean_uint64_xor(v___x_2336_, v___x_2338_);
v___x_2340_ = 16ULL;
v___x_2341_ = lean_uint64_shift_right(v_fold_2339_, v___x_2340_);
v___x_2342_ = lean_uint64_xor(v_fold_2339_, v___x_2341_);
v___x_2343_ = lean_uint64_to_usize(v___x_2342_);
v___x_2344_ = lean_usize_of_nat(v___x_2335_);
v___x_2345_ = ((size_t)1ULL);
v___x_2346_ = lean_usize_sub(v___x_2344_, v___x_2345_);
v___x_2347_ = lean_usize_land(v___x_2343_, v___x_2346_);
v___x_2348_ = lean_array_uget_borrowed(v_x_2327_, v___x_2347_);
lean_inc(v___x_2348_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 2, v___x_2348_);
v___x_2350_ = v___x_2333_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_key_2329_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_value_2330_);
lean_ctor_set(v_reuseFailAlloc_2353_, 2, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2351_; 
v___x_2351_ = lean_array_uset(v_x_2327_, v___x_2347_, v___x_2350_);
v_x_2327_ = v___x_2351_;
v_x_2328_ = v_tail_2331_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(lean_object* v_i_2355_, lean_object* v_source_2356_, lean_object* v_target_2357_){
_start:
{
lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2358_ = lean_array_get_size(v_source_2356_);
v___x_2359_ = lean_nat_dec_lt(v_i_2355_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_dec_ref(v_source_2356_);
lean_dec(v_i_2355_);
return v_target_2357_;
}
else
{
lean_object* v_es_2360_; lean_object* v___x_2361_; lean_object* v_source_2362_; lean_object* v_target_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v_es_2360_ = lean_array_fget(v_source_2356_, v_i_2355_);
v___x_2361_ = lean_box(0);
v_source_2362_ = lean_array_fset(v_source_2356_, v_i_2355_, v___x_2361_);
v_target_2363_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_target_2357_, v_es_2360_);
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = lean_nat_add(v_i_2355_, v___x_2364_);
lean_dec(v_i_2355_);
v_i_2355_ = v___x_2365_;
v_source_2356_ = v_source_2362_;
v_target_2357_ = v_target_2363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12___redArg(lean_object* v_data_2367_){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v_nbuckets_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2368_ = lean_array_get_size(v_data_2367_);
v___x_2369_ = lean_unsigned_to_nat(2u);
v_nbuckets_2370_ = lean_nat_mul(v___x_2368_, v___x_2369_);
v___x_2371_ = lean_unsigned_to_nat(0u);
v___x_2372_ = lean_box(0);
v___x_2373_ = lean_mk_array(v_nbuckets_2370_, v___x_2372_);
v___x_2374_ = lean_array_propagate_mark(v_data_2367_, v___x_2373_);
v___x_2375_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v___x_2371_, v_data_2367_, v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(lean_object* v_a_2376_, lean_object* v_b_2377_, lean_object* v_x_2378_){
_start:
{
if (lean_obj_tag(v_x_2378_) == 0)
{
lean_dec(v_b_2377_);
lean_dec_ref(v_a_2376_);
return v_x_2378_;
}
else
{
lean_object* v_key_2379_; lean_object* v_value_2380_; lean_object* v_tail_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2393_; 
v_key_2379_ = lean_ctor_get(v_x_2378_, 0);
v_value_2380_ = lean_ctor_get(v_x_2378_, 1);
v_tail_2381_ = lean_ctor_get(v_x_2378_, 2);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_x_2378_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2383_ = v_x_2378_;
v_isShared_2384_ = v_isSharedCheck_2393_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_tail_2381_);
lean_inc(v_value_2380_);
lean_inc(v_key_2379_);
lean_dec(v_x_2378_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2393_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
uint8_t v___x_2385_; 
v___x_2385_ = l_Lean_ExprStructEq_beq(v_key_2379_, v_a_2376_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2386_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(v_a_2376_, v_b_2377_, v_tail_2381_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 2, v___x_2386_);
v___x_2388_ = v___x_2383_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_key_2379_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_value_2380_);
lean_ctor_set(v_reuseFailAlloc_2389_, 2, v___x_2386_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
else
{
lean_object* v___x_2391_; 
lean_dec(v_value_2380_);
lean_dec(v_key_2379_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 1, v_b_2377_);
lean_ctor_set(v___x_2383_, 0, v_a_2376_);
v___x_2391_ = v___x_2383_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2376_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_b_2377_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_tail_2381_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_a_2394_, lean_object* v_x_2395_){
_start:
{
if (lean_obj_tag(v_x_2395_) == 0)
{
uint8_t v___x_2396_; 
v___x_2396_ = 0;
return v___x_2396_;
}
else
{
lean_object* v_key_2397_; lean_object* v_tail_2398_; uint8_t v___x_2399_; 
v_key_2397_ = lean_ctor_get(v_x_2395_, 0);
v_tail_2398_ = lean_ctor_get(v_x_2395_, 2);
v___x_2399_ = l_Lean_ExprStructEq_beq(v_key_2397_, v_a_2394_);
if (v___x_2399_ == 0)
{
v_x_2395_ = v_tail_2398_;
goto _start;
}
else
{
return v___x_2399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object* v_a_2401_, lean_object* v_x_2402_){
_start:
{
uint8_t v_res_2403_; lean_object* v_r_2404_; 
v_res_2403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_a_2401_, v_x_2402_);
lean_dec(v_x_2402_);
lean_dec_ref(v_a_2401_);
v_r_2404_ = lean_box(v_res_2403_);
return v_r_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(lean_object* v_m_2405_, lean_object* v_a_2406_, lean_object* v_b_2407_){
_start:
{
lean_object* v_size_2408_; lean_object* v_buckets_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2452_; 
v_size_2408_ = lean_ctor_get(v_m_2405_, 0);
v_buckets_2409_ = lean_ctor_get(v_m_2405_, 1);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_m_2405_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2411_ = v_m_2405_;
v_isShared_2412_ = v_isSharedCheck_2452_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_buckets_2409_);
lean_inc(v_size_2408_);
lean_dec(v_m_2405_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2452_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; uint64_t v___x_2414_; uint64_t v___x_2415_; uint64_t v___x_2416_; uint64_t v_fold_2417_; uint64_t v___x_2418_; uint64_t v___x_2419_; uint64_t v___x_2420_; size_t v___x_2421_; size_t v___x_2422_; size_t v___x_2423_; size_t v___x_2424_; size_t v___x_2425_; lean_object* v_bkt_2426_; uint8_t v___x_2427_; 
v___x_2413_ = lean_array_get_size(v_buckets_2409_);
v___x_2414_ = l_Lean_ExprStructEq_hash(v_a_2406_);
v___x_2415_ = 32ULL;
v___x_2416_ = lean_uint64_shift_right(v___x_2414_, v___x_2415_);
v_fold_2417_ = lean_uint64_xor(v___x_2414_, v___x_2416_);
v___x_2418_ = 16ULL;
v___x_2419_ = lean_uint64_shift_right(v_fold_2417_, v___x_2418_);
v___x_2420_ = lean_uint64_xor(v_fold_2417_, v___x_2419_);
v___x_2421_ = lean_uint64_to_usize(v___x_2420_);
v___x_2422_ = lean_usize_of_nat(v___x_2413_);
v___x_2423_ = ((size_t)1ULL);
v___x_2424_ = lean_usize_sub(v___x_2422_, v___x_2423_);
v___x_2425_ = lean_usize_land(v___x_2421_, v___x_2424_);
v_bkt_2426_ = lean_array_uget_borrowed(v_buckets_2409_, v___x_2425_);
v___x_2427_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_a_2406_, v_bkt_2426_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; lean_object* v_size_x27_2429_; lean_object* v___x_2430_; lean_object* v_buckets_x27_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2428_ = lean_unsigned_to_nat(1u);
v_size_x27_2429_ = lean_nat_add(v_size_2408_, v___x_2428_);
lean_dec(v_size_2408_);
lean_inc(v_bkt_2426_);
v___x_2430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2430_, 0, v_a_2406_);
lean_ctor_set(v___x_2430_, 1, v_b_2407_);
lean_ctor_set(v___x_2430_, 2, v_bkt_2426_);
v_buckets_x27_2431_ = lean_array_uset(v_buckets_2409_, v___x_2425_, v___x_2430_);
v___x_2432_ = lean_unsigned_to_nat(4u);
v___x_2433_ = lean_nat_mul(v_size_x27_2429_, v___x_2432_);
v___x_2434_ = lean_unsigned_to_nat(3u);
v___x_2435_ = lean_nat_div(v___x_2433_, v___x_2434_);
lean_dec(v___x_2433_);
v___x_2436_ = lean_array_get_size(v_buckets_x27_2431_);
v___x_2437_ = lean_nat_dec_le(v___x_2435_, v___x_2436_);
lean_dec(v___x_2435_);
if (v___x_2437_ == 0)
{
lean_object* v_val_2438_; lean_object* v___x_2440_; 
v_val_2438_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12___redArg(v_buckets_x27_2431_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 1, v_val_2438_);
lean_ctor_set(v___x_2411_, 0, v_size_x27_2429_);
v___x_2440_ = v___x_2411_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_size_x27_2429_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v_val_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
else
{
lean_object* v___x_2443_; 
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 1, v_buckets_x27_2431_);
lean_ctor_set(v___x_2411_, 0, v_size_x27_2429_);
v___x_2443_ = v___x_2411_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_size_x27_2429_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_buckets_x27_2431_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
else
{
lean_object* v___x_2445_; lean_object* v_buckets_x27_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2450_; 
lean_inc(v_bkt_2426_);
v___x_2445_ = lean_box(0);
v_buckets_x27_2446_ = lean_array_uset(v_buckets_2409_, v___x_2425_, v___x_2445_);
v___x_2447_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(v_a_2406_, v_b_2407_, v_bkt_2426_);
v___x_2448_ = lean_array_uset(v_buckets_x27_2446_, v___x_2425_, v___x_2447_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 1, v___x_2448_);
v___x_2450_ = v___x_2411_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_size_2408_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2(lean_object* v_a_2453_, lean_object* v_e_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2457_ = lean_st_ref_take(v_a_2453_);
v___x_2458_ = lean_box(0);
v___x_2459_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v___x_2457_, v_e_2454_, v_a_2455_);
v___x_2460_ = lean_st_ref_put(v_a_2453_, v___x_2459_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2461_, lean_object* v_e_2462_, lean_object* v_a_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2(v_a_2461_, v_e_2462_, v_a_2463_);
lean_dec(v_a_2461_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_a_2466_, lean_object* v_x_2467_){
_start:
{
if (lean_obj_tag(v_x_2467_) == 0)
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_box(0);
return v___x_2468_;
}
else
{
lean_object* v_key_2469_; lean_object* v_value_2470_; lean_object* v_tail_2471_; uint8_t v___x_2472_; 
v_key_2469_ = lean_ctor_get(v_x_2467_, 0);
v_value_2470_ = lean_ctor_get(v_x_2467_, 1);
v_tail_2471_ = lean_ctor_get(v_x_2467_, 2);
v___x_2472_ = l_Lean_ExprStructEq_beq(v_key_2469_, v_a_2466_);
if (v___x_2472_ == 0)
{
v_x_2467_ = v_tail_2471_;
goto _start;
}
else
{
lean_object* v___x_2474_; 
lean_inc(v_value_2470_);
v___x_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2474_, 0, v_value_2470_);
return v___x_2474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg___boxed(lean_object* v_a_2475_, lean_object* v_x_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(v_a_2475_, v_x_2476_);
lean_dec(v_x_2476_);
lean_dec_ref(v_a_2475_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(lean_object* v_m_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_buckets_2480_; lean_object* v___x_2481_; uint64_t v___x_2482_; uint64_t v___x_2483_; uint64_t v___x_2484_; uint64_t v_fold_2485_; uint64_t v___x_2486_; uint64_t v___x_2487_; uint64_t v___x_2488_; size_t v___x_2489_; size_t v___x_2490_; size_t v___x_2491_; size_t v___x_2492_; size_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v_buckets_2480_ = lean_ctor_get(v_m_2478_, 1);
v___x_2481_ = lean_array_get_size(v_buckets_2480_);
v___x_2482_ = l_Lean_ExprStructEq_hash(v_a_2479_);
v___x_2483_ = 32ULL;
v___x_2484_ = lean_uint64_shift_right(v___x_2482_, v___x_2483_);
v_fold_2485_ = lean_uint64_xor(v___x_2482_, v___x_2484_);
v___x_2486_ = 16ULL;
v___x_2487_ = lean_uint64_shift_right(v_fold_2485_, v___x_2486_);
v___x_2488_ = lean_uint64_xor(v_fold_2485_, v___x_2487_);
v___x_2489_ = lean_uint64_to_usize(v___x_2488_);
v___x_2490_ = lean_usize_of_nat(v___x_2481_);
v___x_2491_ = ((size_t)1ULL);
v___x_2492_ = lean_usize_sub(v___x_2490_, v___x_2491_);
v___x_2493_ = lean_usize_land(v___x_2489_, v___x_2492_);
v___x_2494_ = lean_array_uget_borrowed(v_buckets_2480_, v___x_2493_);
v___x_2495_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(v_a_2479_, v___x_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_m_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(v_m_2496_, v_a_2497_);
lean_dec_ref(v_a_2497_);
lean_dec_ref(v_m_2496_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2499_, lean_object* v_x_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_apply_1(v_x_2500_, lean_box(0));
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2506_, lean_object* v_x_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(v_00_u03b1_2506_, v_x_2507_, v___y_2508_, v___y_2509_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
return v_res_2511_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2513_; lean_object* v_dummy_2514_; 
v___x_2513_ = lean_box(0);
v_dummy_2514_ = l_Lean_Expr_sort___override(v___x_2513_);
return v_dummy_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object* v_pre_2515_, lean_object* v_post_2516_, size_t v_sz_2517_, size_t v_i_2518_, lean_object* v_bs_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_usize_dec_lt(v_i_2518_, v_sz_2517_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; 
lean_dec_ref(v_post_2516_);
lean_dec_ref(v_pre_2515_);
v___x_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_bs_2519_);
return v___x_2525_;
}
else
{
lean_object* v_v_2526_; lean_object* v___x_2527_; lean_object* v_bs_x27_2528_; lean_object* v___x_2529_; 
v_v_2526_ = lean_array_uget(v_bs_2519_, v_i_2518_);
v___x_2527_ = lean_unsigned_to_nat(0u);
v_bs_x27_2528_ = lean_array_uset(v_bs_2519_, v_i_2518_, v___x_2527_);
lean_inc_ref(v_post_2516_);
lean_inc_ref(v_pre_2515_);
v___x_2529_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2515_, v_post_2516_, v_v_2526_, v___y_2520_, v___y_2521_, v___y_2522_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; size_t v___x_2531_; size_t v___x_2532_; lean_object* v___x_2533_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2531_ = ((size_t)1ULL);
v___x_2532_ = lean_usize_add(v_i_2518_, v___x_2531_);
v___x_2533_ = lean_array_uset(v_bs_x27_2528_, v_i_2518_, v_a_2530_);
v_i_2518_ = v___x_2532_;
v_bs_2519_ = v___x_2533_;
goto _start;
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec_ref(v_bs_x27_2528_);
lean_dec_ref(v_post_2516_);
lean_dec_ref(v_pre_2515_);
v_a_2535_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2529_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2529_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(lean_object* v_pre_2543_, lean_object* v_post_2544_, lean_object* v_x_2545_, lean_object* v_x_2546_, lean_object* v_x_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
if (lean_obj_tag(v_x_2545_) == 5)
{
lean_object* v_fn_2552_; lean_object* v_arg_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v_fn_2552_ = lean_ctor_get(v_x_2545_, 0);
lean_inc_ref(v_fn_2552_);
v_arg_2553_ = lean_ctor_get(v_x_2545_, 1);
lean_inc_ref(v_arg_2553_);
lean_dec_ref_known(v_x_2545_, 2);
v___x_2554_ = lean_array_set(v_x_2546_, v_x_2547_, v_arg_2553_);
v___x_2555_ = lean_unsigned_to_nat(1u);
v___x_2556_ = lean_nat_sub(v_x_2547_, v___x_2555_);
lean_dec(v_x_2547_);
v_x_2545_ = v_fn_2552_;
v_x_2546_ = v___x_2554_;
v_x_2547_ = v___x_2556_;
goto _start;
}
else
{
lean_object* v___x_2558_; 
lean_dec(v_x_2547_);
lean_inc_ref(v_post_2544_);
lean_inc_ref(v_pre_2543_);
v___x_2558_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2543_, v_post_2544_, v_x_2545_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; size_t v_sz_2560_; size_t v___x_2561_; lean_object* v___x_2562_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v_sz_2560_ = lean_array_size(v_x_2546_);
v___x_2561_ = ((size_t)0ULL);
lean_inc_ref(v_post_2544_);
lean_inc_ref(v_pre_2543_);
v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_2543_, v_post_2544_, v_sz_2560_, v___x_2561_, v_x_2546_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = l_Lean_mkAppN(v_a_2559_, v_a_2563_);
lean_dec(v_a_2563_);
v___x_2565_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2543_, v_post_2544_, v___x_2564_, v___y_2548_, v___y_2549_, v___y_2550_);
return v___x_2565_;
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v_a_2559_);
lean_dec_ref(v_post_2544_);
lean_dec_ref(v_pre_2543_);
v_a_2566_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2562_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2562_);
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
else
{
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_post_2544_);
lean_dec_ref(v_pre_2543_);
return v___x_2558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object* v___x_2574_, lean_object* v_pre_2575_, lean_object* v_e_2576_, lean_object* v_post_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_Core_checkSystem(v___x_2574_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v___x_2583_; 
lean_dec_ref_known(v___x_2582_, 1);
lean_inc_ref(v_pre_2575_);
lean_inc(v___y_2580_);
lean_inc_ref(v___y_2579_);
lean_inc_ref(v_e_2576_);
v___x_2583_ = lean_apply_4(v_pre_2575_, v_e_2576_, v___y_2579_, v___y_2580_, lean_box(0));
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2699_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2699_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2699_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___y_2589_; 
switch(lean_obj_tag(v_a_2584_))
{
case 0:
{
lean_object* v_e_2689_; lean_object* v___x_2691_; 
lean_dec_ref(v_post_2577_);
lean_dec_ref(v_e_2576_);
lean_dec_ref(v_pre_2575_);
v_e_2689_ = lean_ctor_get(v_a_2584_, 0);
lean_inc_ref(v_e_2689_);
lean_dec_ref_known(v_a_2584_, 1);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v_e_2689_);
v___x_2691_ = v___x_2586_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_e_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
case 1:
{
lean_object* v_e_2693_; lean_object* v___x_2694_; 
lean_del_object(v___x_2586_);
lean_dec_ref(v_e_2576_);
v_e_2693_ = lean_ctor_get(v_a_2584_, 0);
lean_inc_ref(v_e_2693_);
lean_dec_ref_known(v_a_2584_, 1);
lean_inc_ref(v_post_2577_);
lean_inc_ref(v_pre_2575_);
v___x_2694_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2575_, v_post_2577_, v_e_2693_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2696_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2694_, 1);
v___x_2696_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v_a_2695_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2696_;
}
else
{
lean_dec_ref(v_post_2577_);
lean_dec_ref(v_pre_2575_);
return v___x_2694_;
}
}
default: 
{
lean_object* v_e_x3f_2697_; 
lean_del_object(v___x_2586_);
v_e_x3f_2697_ = lean_ctor_get(v_a_2584_, 0);
lean_inc(v_e_x3f_2697_);
lean_dec_ref_known(v_a_2584_, 1);
if (lean_obj_tag(v_e_x3f_2697_) == 0)
{
v___y_2589_ = v_e_2576_;
goto v___jp_2588_;
}
else
{
lean_object* v_val_2698_; 
lean_dec_ref(v_e_2576_);
v_val_2698_ = lean_ctor_get(v_e_x3f_2697_, 0);
lean_inc(v_val_2698_);
lean_dec_ref_known(v_e_x3f_2697_, 1);
v___y_2589_ = v_val_2698_;
goto v___jp_2588_;
}
}
}
v___jp_2588_:
{
switch(lean_obj_tag(v___y_2589_))
{
case 7:
{
lean_object* v_binderName_2590_; lean_object* v_binderType_2591_; lean_object* v_body_2592_; uint8_t v_binderInfo_2593_; lean_object* v___x_2594_; 
v_binderName_2590_ = lean_ctor_get(v___y_2589_, 0);
v_binderType_2591_ = lean_ctor_get(v___y_2589_, 1);
v_body_2592_ = lean_ctor_get(v___y_2589_, 2);
v_binderInfo_2593_ = lean_ctor_get_uint8(v___y_2589_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2591_);
lean_inc_ref(v_post_2577_);
lean_inc_ref(v_pre_2575_);
v___x_2594_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2575_, v_post_2577_, v_binderType_2591_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2596_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___x_2594_, 1);
lean_inc_ref(v_body_2592_);
lean_inc_ref(v_post_2577_);
lean_inc_ref(v_pre_2575_);
v___x_2596_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2575_, v_post_2577_, v_body_2592_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; size_t v___x_2598_; size_t v___x_2599_; uint8_t v___x_2600_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v___x_2598_ = lean_ptr_addr(v_binderType_2591_);
v___x_2599_ = lean_ptr_addr(v_a_2595_);
v___x_2600_ = lean_usize_dec_eq(v___x_2598_, v___x_2599_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_inc(v_binderName_2590_);
lean_dec_ref_known(v___y_2589_, 3);
v___x_2601_ = l_Lean_Expr_forallE___override(v_binderName_2590_, v_a_2595_, v_a_2597_, v_binderInfo_2593_);
v___x_2602_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___x_2601_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2602_;
}
else
{
size_t v___x_2603_; size_t v___x_2604_; uint8_t v___x_2605_; 
v___x_2603_ = lean_ptr_addr(v_body_2592_);
v___x_2604_ = lean_ptr_addr(v_a_2597_);
v___x_2605_ = lean_usize_dec_eq(v___x_2603_, v___x_2604_);
if (v___x_2605_ == 0)
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_inc(v_binderName_2590_);
lean_dec_ref_known(v___y_2589_, 3);
v___x_2606_ = l_Lean_Expr_forallE___override(v_binderName_2590_, v_a_2595_, v_a_2597_, v_binderInfo_2593_);
v___x_2607_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___x_2606_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2607_;
}
else
{
uint8_t v___x_2608_; 
v___x_2608_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2593_, v_binderInfo_2593_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_inc(v_binderName_2590_);
lean_dec_ref_known(v___y_2589_, 3);
v___x_2609_ = l_Lean_Expr_forallE___override(v_binderName_2590_, v_a_2595_, v_a_2597_, v_binderInfo_2593_);
v___x_2610_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___x_2609_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2610_;
}
else
{
lean_object* v___x_2611_; 
lean_dec(v_a_2597_);
lean_dec(v_a_2595_);
v___x_2611_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___y_2589_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2611_;
}
}
}
}
else
{
lean_dec(v_a_2595_);
lean_dec_ref_known(v___y_2589_, 3);
lean_dec_ref(v_post_2577_);
lean_dec_ref(v_pre_2575_);
return v___x_2596_;
}
}
else
{
lean_dec_ref_known(v___y_2589_, 3);
lean_dec_ref(v_post_2577_);
lean_dec_ref(v_pre_2575_);
return v___x_2594_;
}
}
case 6:
{
lean_object* v_binderName_2612_; lean_object* v_binderType_2613_; lean_object* v_body_2614_; uint8_t v_binderInfo_2615_; lean_object* v___x_2616_; 
v_binderName_2612_ = lean_ctor_get(v___y_2589_, 0);
v_binderType_2613_ = lean_ctor_get(v___y_2589_, 1);
v_body_2614_ = lean_ctor_get(v___y_2589_, 2);
v_binderInfo_2615_ = lean_ctor_get_uint8(v___y_2589_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2613_);
lean_inc_ref(v_post_2577_);
lean_inc_ref(v_pre_2575_);
v___x_2616_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2575_, v_post_2577_, v_binderType_2613_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2618_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
lean_inc_ref(v_body_2614_);
lean_inc_ref(v_post_2577_);
lean_inc_ref(v_pre_2575_);
v___x_2618_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2575_, v_post_2577_, v_body_2614_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; size_t v___x_2620_; size_t v___x_2621_; uint8_t v___x_2622_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2620_ = lean_ptr_addr(v_binderType_2613_);
v___x_2621_ = lean_ptr_addr(v_a_2617_);
v___x_2622_ = lean_usize_dec_eq(v___x_2620_, v___x_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_inc(v_binderName_2612_);
lean_dec_ref_known(v___y_2589_, 3);
v___x_2623_ = l_Lean_Expr_lam___override(v_binderName_2612_, v_a_2617_, v_a_2619_, v_binderInfo_2615_);
v___x_2624_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___x_2623_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2624_;
}
else
{
size_t v___x_2625_; size_t v___x_2626_; uint8_t v___x_2627_; 
v___x_2625_ = lean_ptr_addr(v_body_2614_);
v___x_2626_ = lean_ptr_addr(v_a_2619_);
v___x_2627_ = lean_usize_dec_eq(v___x_2625_, v___x_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
lean_inc(v_binderName_2612_);
lean_dec_ref_known(v___y_2589_, 3);
v___x_2628_ = l_Lean_Expr_lam___override(v_binderName_2612_, v_a_2617_, v_a_2619_, v_binderInfo_2615_);
v___x_2629_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___x_2628_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2629_;
}
else
{
uint8_t v___x_2630_; 
v___x_2630_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2615_, v_binderInfo_2615_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_inc(v_binderName_2612_);
lean_dec_ref_known(v___y_2589_, 3);
v___x_2631_ = l_Lean_Expr_lam___override(v_binderName_2612_, v_a_2617_, v_a_2619_, v_binderInfo_2615_);
v___x_2632_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___x_2631_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2632_;
}
else
{
lean_object* v___x_2633_; 
lean_dec(v_a_2619_);
lean_dec(v_a_2617_);
v___x_2633_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___y_2589_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2633_;
}
}
}
}
else
{
lean_dec(v_a_2617_);
lean_dec_ref_known(v___y_2589_, 3);
lean_dec_ref(v_post_2577_);
lean_dec_ref(v_pre_2575_);
return v___x_2618_;
}
}
else
{
lean_dec_ref_known(v___y_2589_, 3);
lean_dec_ref(v_post_2577_);
lean_dec_ref(v_pre_2575_);
return v___x_2616_;
}
}
case 8:
{
lean_object* v_declName_2634_; lean_object* v_type_2635_; lean_object* v_value_2636_; lean_object* v_body_2637_; uint8_t v_nondep_2638_; lean_object* v___x_2639_; 
v_declName_2634_ = lean_ctor_get(v___y_2589_, 0);
v_type_2635_ = lean_ctor_get(v___y_2589_, 1);
v_value_2636_ = lean_ctor_get(v___y_2589_, 2);
v_body_2637_ = lean_ctor_get(v___y_2589_, 3);
v_nondep_2638_ = lean_ctor_get_uint8(v___y_2589_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2635_);
lean_inc_ref(v_post_2577_);
lean_inc_ref(v_pre_2575_);
v___x_2639_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2575_, v_post_2577_, v_type_2635_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2641_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___x_2639_, 1);
lean_inc_ref(v_value_2636_);
lean_inc_ref(v_post_2577_);
lean_inc_ref(v_pre_2575_);
v___x_2641_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2575_, v_post_2577_, v_value_2636_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2643_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
lean_inc_ref(v_body_2637_);
lean_inc_ref(v_post_2577_);
lean_inc_ref(v_pre_2575_);
v___x_2643_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2575_, v_post_2577_, v_body_2637_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; size_t v___x_2645_; size_t v___x_2646_; uint8_t v___x_2647_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2645_ = lean_ptr_addr(v_type_2635_);
v___x_2646_ = lean_ptr_addr(v_a_2640_);
v___x_2647_ = lean_usize_dec_eq(v___x_2645_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_inc(v_declName_2634_);
lean_dec_ref_known(v___y_2589_, 4);
v___x_2648_ = l_Lean_Expr_letE___override(v_declName_2634_, v_a_2640_, v_a_2642_, v_a_2644_, v_nondep_2638_);
v___x_2649_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___x_2648_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2649_;
}
else
{
size_t v___x_2650_; size_t v___x_2651_; uint8_t v___x_2652_; 
v___x_2650_ = lean_ptr_addr(v_value_2636_);
v___x_2651_ = lean_ptr_addr(v_a_2642_);
v___x_2652_ = lean_usize_dec_eq(v___x_2650_, v___x_2651_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_inc(v_declName_2634_);
lean_dec_ref_known(v___y_2589_, 4);
v___x_2653_ = l_Lean_Expr_letE___override(v_declName_2634_, v_a_2640_, v_a_2642_, v_a_2644_, v_nondep_2638_);
v___x_2654_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___x_2653_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2654_;
}
else
{
size_t v___x_2655_; size_t v___x_2656_; uint8_t v___x_2657_; 
v___x_2655_ = lean_ptr_addr(v_body_2637_);
v___x_2656_ = lean_ptr_addr(v_a_2644_);
v___x_2657_ = lean_usize_dec_eq(v___x_2655_, v___x_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_inc(v_declName_2634_);
lean_dec_ref_known(v___y_2589_, 4);
v___x_2658_ = l_Lean_Expr_letE___override(v_declName_2634_, v_a_2640_, v_a_2642_, v_a_2644_, v_nondep_2638_);
v___x_2659_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___x_2658_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2659_;
}
else
{
lean_object* v___x_2660_; 
lean_dec(v_a_2644_);
lean_dec(v_a_2642_);
lean_dec(v_a_2640_);
v___x_2660_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___y_2589_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2660_;
}
}
}
}
else
{
lean_dec(v_a_2642_);
lean_dec(v_a_2640_);
lean_dec_ref_known(v___y_2589_, 4);
lean_dec_ref(v_post_2577_);
lean_dec_ref(v_pre_2575_);
return v___x_2643_;
}
}
else
{
lean_dec(v_a_2640_);
lean_dec_ref_known(v___y_2589_, 4);
lean_dec_ref(v_post_2577_);
lean_dec_ref(v_pre_2575_);
return v___x_2641_;
}
}
else
{
lean_dec_ref_known(v___y_2589_, 4);
lean_dec_ref(v_post_2577_);
lean_dec_ref(v_pre_2575_);
return v___x_2639_;
}
}
case 5:
{
lean_object* v_dummy_2661_; lean_object* v_nargs_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_dummy_2661_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0);
v_nargs_2662_ = l_Lean_Expr_getAppNumArgs(v___y_2589_);
lean_inc(v_nargs_2662_);
v___x_2663_ = lean_mk_array(v_nargs_2662_, v_dummy_2661_);
v___x_2664_ = lean_unsigned_to_nat(1u);
v___x_2665_ = lean_nat_sub(v_nargs_2662_, v___x_2664_);
lean_dec(v_nargs_2662_);
v___x_2666_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_pre_2575_, v_post_2577_, v___y_2589_, v___x_2663_, v___x_2665_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2666_;
}
case 10:
{
lean_object* v_data_2667_; lean_object* v_expr_2668_; lean_object* v___x_2669_; 
v_data_2667_ = lean_ctor_get(v___y_2589_, 0);
v_expr_2668_ = lean_ctor_get(v___y_2589_, 1);
lean_inc_ref(v_expr_2668_);
lean_inc_ref(v_post_2577_);
lean_inc_ref(v_pre_2575_);
v___x_2669_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2575_, v_post_2577_, v_expr_2668_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; size_t v___x_2671_; size_t v___x_2672_; uint8_t v___x_2673_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2671_ = lean_ptr_addr(v_expr_2668_);
v___x_2672_ = lean_ptr_addr(v_a_2670_);
v___x_2673_ = lean_usize_dec_eq(v___x_2671_, v___x_2672_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_inc(v_data_2667_);
lean_dec_ref_known(v___y_2589_, 2);
v___x_2674_ = l_Lean_Expr_mdata___override(v_data_2667_, v_a_2670_);
v___x_2675_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___x_2674_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2675_;
}
else
{
lean_object* v___x_2676_; 
lean_dec(v_a_2670_);
v___x_2676_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___y_2589_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2676_;
}
}
else
{
lean_dec_ref_known(v___y_2589_, 2);
lean_dec_ref(v_post_2577_);
lean_dec_ref(v_pre_2575_);
return v___x_2669_;
}
}
case 11:
{
lean_object* v_typeName_2677_; lean_object* v_idx_2678_; lean_object* v_struct_2679_; lean_object* v___x_2680_; 
v_typeName_2677_ = lean_ctor_get(v___y_2589_, 0);
v_idx_2678_ = lean_ctor_get(v___y_2589_, 1);
v_struct_2679_ = lean_ctor_get(v___y_2589_, 2);
lean_inc_ref(v_struct_2679_);
lean_inc_ref(v_post_2577_);
lean_inc_ref(v_pre_2575_);
v___x_2680_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2575_, v_post_2577_, v_struct_2679_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; size_t v___x_2682_; size_t v___x_2683_; uint8_t v___x_2684_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = lean_ptr_addr(v_struct_2679_);
v___x_2683_ = lean_ptr_addr(v_a_2681_);
v___x_2684_ = lean_usize_dec_eq(v___x_2682_, v___x_2683_);
if (v___x_2684_ == 0)
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
lean_inc(v_idx_2678_);
lean_inc(v_typeName_2677_);
lean_dec_ref_known(v___y_2589_, 3);
v___x_2685_ = l_Lean_Expr_proj___override(v_typeName_2677_, v_idx_2678_, v_a_2681_);
v___x_2686_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___x_2685_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2686_;
}
else
{
lean_object* v___x_2687_; 
lean_dec(v_a_2681_);
v___x_2687_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___y_2589_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2687_;
}
}
else
{
lean_dec_ref_known(v___y_2589_, 3);
lean_dec_ref(v_post_2577_);
lean_dec_ref(v_pre_2575_);
return v___x_2680_;
}
}
default: 
{
lean_object* v___x_2688_; 
v___x_2688_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2575_, v_post_2577_, v___y_2589_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2688_;
}
}
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec_ref(v_post_2577_);
lean_dec_ref(v_e_2576_);
lean_dec_ref(v_pre_2575_);
v_a_2700_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2583_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2583_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec_ref(v_post_2577_);
lean_dec_ref(v_e_2576_);
lean_dec_ref(v_pre_2575_);
v_a_2708_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2582_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2582_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object* v___x_2716_, lean_object* v_pre_2717_, lean_object* v_e_2718_, lean_object* v_post_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(v___x_2716_, v_pre_2717_, v_e_2718_, v_post_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(lean_object* v_pre_2725_, lean_object* v_post_2726_, lean_object* v_e_2727_, lean_object* v_a_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_inc(v_a_2728_);
v___x_2732_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2732_, 0, lean_box(0));
lean_closure_set(v___x_2732_, 1, lean_box(0));
lean_closure_set(v___x_2732_, 2, v_a_2728_);
v___x_2733_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___x_2732_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2765_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2765_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2765_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(v_a_2734_, v_e_2727_);
lean_dec(v_a_2734_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v___x_2739_; lean_object* v___f_2740_; lean_object* v___x_2741_; 
lean_del_object(v___x_2736_);
v___x_2739_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___closed__0));
lean_inc_ref(v_e_2727_);
v___f_2740_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed), 8, 4);
lean_closure_set(v___f_2740_, 0, v___x_2739_);
lean_closure_set(v___f_2740_, 1, v_pre_2725_);
lean_closure_set(v___f_2740_, 2, v_e_2727_);
lean_closure_set(v___f_2740_, 3, v_post_2726_);
v___x_2741_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v___f_2740_, v_a_2728_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___f_2743_; lean_object* v___x_2744_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc_n(v_a_2742_, 2);
lean_dec_ref_known(v___x_2741_, 1);
lean_inc(v_a_2728_);
v___f_2743_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2743_, 0, v_a_2728_);
lean_closure_set(v___f_2743_, 1, v_e_2727_);
lean_closure_set(v___f_2743_, 2, v_a_2742_);
v___x_2744_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___f_2743_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2751_ == 0)
{
lean_object* v_unused_2752_; 
v_unused_2752_ = lean_ctor_get(v___x_2744_, 0);
lean_dec(v_unused_2752_);
v___x_2746_ = v___x_2744_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_dec(v___x_2744_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v_a_2742_);
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2742_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_a_2742_);
v_a_2753_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2744_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2744_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
else
{
lean_dec_ref(v_e_2727_);
return v___x_2741_;
}
}
else
{
lean_object* v_val_2761_; lean_object* v___x_2763_; 
lean_dec_ref(v_e_2727_);
lean_dec_ref(v_post_2726_);
lean_dec_ref(v_pre_2725_);
v_val_2761_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_val_2761_);
lean_dec_ref_known(v___x_2738_, 1);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v_val_2761_);
v___x_2763_ = v___x_2736_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_val_2761_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec_ref(v_e_2727_);
lean_dec_ref(v_post_2726_);
lean_dec_ref(v_pre_2725_);
v_a_2766_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2733_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2733_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(lean_object* v_pre_2774_, lean_object* v_post_2775_, lean_object* v_e_2776_, lean_object* v_a_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v___x_2781_; 
lean_inc_ref(v_post_2775_);
lean_inc(v___y_2779_);
lean_inc_ref(v___y_2778_);
lean_inc_ref(v_e_2776_);
v___x_2781_ = lean_apply_4(v_post_2775_, v_e_2776_, v___y_2778_, v___y_2779_, lean_box(0));
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2800_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2800_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2800_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
switch(lean_obj_tag(v_a_2782_))
{
case 0:
{
lean_object* v_e_2786_; lean_object* v___x_2788_; 
lean_dec_ref(v_e_2776_);
lean_dec_ref(v_post_2775_);
lean_dec_ref(v_pre_2774_);
v_e_2786_ = lean_ctor_get(v_a_2782_, 0);
lean_inc_ref(v_e_2786_);
lean_dec_ref_known(v_a_2782_, 1);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v_e_2786_);
v___x_2788_ = v___x_2784_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_e_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
case 1:
{
lean_object* v_e_2790_; lean_object* v___x_2791_; 
lean_del_object(v___x_2784_);
lean_dec_ref(v_e_2776_);
v_e_2790_ = lean_ctor_get(v_a_2782_, 0);
lean_inc_ref(v_e_2790_);
lean_dec_ref_known(v_a_2782_, 1);
v___x_2791_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2774_, v_post_2775_, v_e_2790_, v_a_2777_, v___y_2778_, v___y_2779_);
return v___x_2791_;
}
default: 
{
lean_object* v_e_x3f_2792_; 
lean_dec_ref(v_post_2775_);
lean_dec_ref(v_pre_2774_);
v_e_x3f_2792_ = lean_ctor_get(v_a_2782_, 0);
lean_inc(v_e_x3f_2792_);
lean_dec_ref_known(v_a_2782_, 1);
if (lean_obj_tag(v_e_x3f_2792_) == 0)
{
lean_object* v___x_2794_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v_e_2776_);
v___x_2794_ = v___x_2784_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_e_2776_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
else
{
lean_object* v_val_2796_; lean_object* v___x_2798_; 
lean_dec_ref(v_e_2776_);
v_val_2796_ = lean_ctor_get(v_e_x3f_2792_, 0);
lean_inc(v_val_2796_);
lean_dec_ref_known(v_e_x3f_2792_, 1);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v_val_2796_);
v___x_2798_ = v___x_2784_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_val_2796_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec_ref(v_e_2776_);
lean_dec_ref(v_post_2775_);
lean_dec_ref(v_pre_2774_);
v_a_2801_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2781_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2781_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_2809_, lean_object* v_post_2810_, lean_object* v_e_2811_, lean_object* v_a_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2809_, v_post_2810_, v_e_2811_, v_a_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v_a_2812_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_2817_, lean_object* v_post_2818_, lean_object* v_sz_2819_, lean_object* v_i_2820_, lean_object* v_bs_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
size_t v_sz_boxed_2826_; size_t v_i_boxed_2827_; lean_object* v_res_2828_; 
v_sz_boxed_2826_ = lean_unbox_usize(v_sz_2819_);
lean_dec(v_sz_2819_);
v_i_boxed_2827_ = lean_unbox_usize(v_i_2820_);
lean_dec(v_i_2820_);
v_res_2828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_2817_, v_post_2818_, v_sz_boxed_2826_, v_i_boxed_2827_, v_bs_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_2829_, lean_object* v_post_2830_, lean_object* v_x_2831_, lean_object* v_x_2832_, lean_object* v_x_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_pre_2829_, v_post_2830_, v_x_2831_, v_x_2832_, v_x_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___boxed(lean_object* v_pre_2839_, lean_object* v_post_2840_, lean_object* v_e_2841_, lean_object* v_a_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2839_, v_post_2840_, v_e_2841_, v_a_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v_a_2842_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_object* v_00_u03b1_2847_, lean_object* v_x_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_apply_1(v_x_2848_, lean_box(0));
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2854_, lean_object* v_x_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(v_00_u03b1_2854_, v_x_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
return v_res_2859_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__1, &l_Lean_Expr_checkMaxShared___closed__1_once, _init_l_Lean_Expr_checkMaxShared___closed__1);
v___x_2861_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2861_, 0, lean_box(0));
lean_closure_set(v___x_2861_, 1, lean_box(0));
lean_closure_set(v___x_2861_, 2, v___x_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(lean_object* v_input_2862_, lean_object* v_pre_2863_, lean_object* v_post_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v_a_2870_; lean_object* v___x_2871_; 
v___x_2868_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0);
v___x_2869_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_2868_, v___y_2865_, v___y_2866_);
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref(v___x_2869_);
v___x_2871_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2863_, v_post_2864_, v_input_2862_, v_a_2870_, v___y_2865_, v___y_2866_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2873_, 0, lean_box(0));
lean_closure_set(v___x_2873_, 1, lean_box(0));
lean_closure_set(v___x_2873_, 2, v_a_2870_);
v___x_2874_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_2873_, v___y_2865_, v___y_2866_);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; 
v_unused_2882_ = lean_ctor_get(v___x_2874_, 0);
lean_dec(v_unused_2882_);
v___x_2876_ = v___x_2874_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_dec(v___x_2874_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 0, v_a_2872_);
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2872_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
else
{
lean_dec(v_a_2870_);
return v___x_2871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___boxed(lean_object* v_input_2883_, lean_object* v_pre_2884_, lean_object* v_post_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_input_2883_, v_pre_2884_, v_post_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object* v_e_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
uint8_t v___x_2896_; 
v___x_2896_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_2892_);
if (v___x_2896_ == 0)
{
lean_object* v_pre_2897_; lean_object* v___f_2898_; lean_object* v___x_2899_; 
v_pre_2897_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__0));
v___f_2898_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__1));
v___x_2899_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_e_2892_, v_pre_2897_, v___f_2898_, v_a_2893_, v_a_2894_);
return v___x_2899_;
}
else
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2900_, 0, v_e_2892_);
return v___x_2900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___boxed(lean_object* v_e_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Meta_Sym_normalizeLevels(v_e_2901_, v_a_2902_, v_a_2903_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_2906_, lean_object* v_m_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(v_m_2907_, v_a_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2910_, lean_object* v_m_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_00_u03b2_2910_, v_m_2911_, v_a_2912_);
lean_dec_ref(v_a_2912_);
lean_dec_ref(v_m_2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_2914_, lean_object* v_ref_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2915_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2920_, lean_object* v_ref_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_2920_, v_ref_2921_, v___y_2922_, v___y_2923_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9(v_00_u03b1_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6(lean_object* v_00_u03b1_2936_, lean_object* v_x_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v_x_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b1_2943_, lean_object* v_x_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6(v_00_u03b1_2943_, v_x_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_2950_, lean_object* v_m_2951_, lean_object* v_a_2952_, lean_object* v_b_2953_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v_m_2951_, v_a_2952_, v_b_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_2955_, lean_object* v_a_2956_, lean_object* v_x_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(v_a_2956_, v_x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2959_, lean_object* v_a_2960_, lean_object* v_x_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5(v_00_u03b2_2959_, v_a_2960_, v_x_2961_);
lean_dec(v_x_2961_);
lean_dec_ref(v_a_2960_);
return v_res_2962_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_2963_, lean_object* v_a_2964_, lean_object* v_x_2965_){
_start:
{
uint8_t v___x_2966_; 
v___x_2966_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_a_2964_, v_x_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_2967_, lean_object* v_a_2968_, lean_object* v_x_2969_){
_start:
{
uint8_t v_res_2970_; lean_object* v_r_2971_; 
v_res_2970_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_2967_, v_a_2968_, v_x_2969_);
lean_dec(v_x_2969_);
lean_dec_ref(v_a_2968_);
v_r_2971_ = lean_box(v_res_2970_);
return v_r_2971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_2972_, lean_object* v_data_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12___redArg(v_data_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13(lean_object* v_00_u03b2_2975_, lean_object* v_a_2976_, lean_object* v_b_2977_, lean_object* v_x_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(v_a_2976_, v_b_2977_, v_x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13(lean_object* v_00_u03b2_2980_, lean_object* v_i_2981_, lean_object* v_source_2982_, lean_object* v_target_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v_i_2981_, v_source_2982_, v_target_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14(lean_object* v_00_u03b2_2985_, lean_object* v_x_2986_, lean_object* v_x_2987_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_x_2986_, v_x_2987_);
return v___x_2988_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
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
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
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
