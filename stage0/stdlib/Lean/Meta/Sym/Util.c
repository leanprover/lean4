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
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Expr_updateAppN(lean_object*, lean_object*, lean_object*);
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
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_mkNotS_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_mkNotS_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_mkNotS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Sym_mkNotS___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_mkNotS___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_mkNotS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_mkNotS___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Sym_mkNotS___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_mkNotS___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkNotS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkNotS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_mkAndS_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_mkAndS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_mkAndS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_Sym_mkAndS___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_mkAndS___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_mkAndS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_mkAndS___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Meta_Sym_mkAndS___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_mkAndS___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkAndS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkAndS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_mkOrS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_Meta_Sym_mkOrS___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_mkOrS___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_mkOrS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_mkOrS___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_Meta_Sym_mkOrS___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_mkOrS___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkOrS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkOrS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_mkExistsS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l_Lean_Meta_Sym_mkExistsS___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_mkExistsS___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_mkExistsS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_mkExistsS___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l_Lean_Meta_Sym_mkExistsS___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_mkExistsS___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkExistsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkExistsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_2255__boxed_1368_; size_t v_x_2256__boxed_1369_; lean_object* v_res_1370_; 
v_x_2255__boxed_1368_ = lean_unbox_usize(v_x_1364_);
lean_dec(v_x_1364_);
v_x_2256__boxed_1369_ = lean_unbox_usize(v_x_1365_);
lean_dec(v_x_1365_);
v_res_1370_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1363_, v_x_2255__boxed_1368_, v_x_2256__boxed_1369_, v_x_1366_, v_x_1367_);
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
lean_object* v___x_1382_; lean_object* v_mctx_1383_; lean_object* v_cache_1384_; lean_object* v_zetaDeltaFVarIds_1385_; lean_object* v_postponed_1386_; lean_object* v_diag_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1415_; 
v___x_1382_ = lean_st_ref_take(v___y_1380_);
v_mctx_1383_ = lean_ctor_get(v___x_1382_, 0);
v_cache_1384_ = lean_ctor_get(v___x_1382_, 1);
v_zetaDeltaFVarIds_1385_ = lean_ctor_get(v___x_1382_, 2);
v_postponed_1386_ = lean_ctor_get(v___x_1382_, 3);
v_diag_1387_ = lean_ctor_get(v___x_1382_, 4);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1389_ = v___x_1382_;
v_isShared_1390_ = v_isSharedCheck_1415_;
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
v_isShared_1390_ = v_isSharedCheck_1415_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_depth_1391_; lean_object* v_levelAssignDepth_1392_; lean_object* v_lmvarCounter_1393_; lean_object* v_mvarCounter_1394_; lean_object* v_lDecls_1395_; lean_object* v_decls_1396_; lean_object* v_userNames_1397_; lean_object* v_lAssignment_1398_; lean_object* v_eAssignment_1399_; lean_object* v_dAssignment_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1414_; 
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
v_isSharedCheck_1414_ = !lean_is_exclusive(v_mctx_1383_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1402_ = v_mctx_1383_;
v_isShared_1403_ = v_isSharedCheck_1414_;
goto v_resetjp_1401_;
}
else
{
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
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1414_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1404_ = lean_box(0);
v___x_1405_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_eAssignment_1399_, v_mvarId_1378_, v_val_1379_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 8, v___x_1405_);
v___x_1407_ = v___x_1402_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_depth_1391_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_levelAssignDepth_1392_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_lmvarCounter_1393_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v_mvarCounter_1394_);
lean_ctor_set(v_reuseFailAlloc_1413_, 4, v_lDecls_1395_);
lean_ctor_set(v_reuseFailAlloc_1413_, 5, v_decls_1396_);
lean_ctor_set(v_reuseFailAlloc_1413_, 6, v_userNames_1397_);
lean_ctor_set(v_reuseFailAlloc_1413_, 7, v_lAssignment_1398_);
lean_ctor_set(v_reuseFailAlloc_1413_, 8, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1413_, 9, v_dAssignment_1400_);
v___x_1407_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1409_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1407_);
v___x_1409_ = v___x_1389_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_cache_1384_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v_zetaDeltaFVarIds_1385_);
lean_ctor_set(v_reuseFailAlloc_1412_, 3, v_postponed_1386_);
lean_ctor_set(v_reuseFailAlloc_1412_, 4, v_diag_1387_);
v___x_1409_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_st_ref_put(v___y_1380_, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1404_);
return v___x_1411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg___boxed(lean_object* v_mvarId_1416_, lean_object* v_val_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1416_, v_val_1417_, v___y_1418_);
lean_dec(v___y_1418_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object* v_mvarId_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v___x_1429_; 
lean_inc(v_mvarId_1421_);
v___x_1429_ = l_Lean_MVarId_getDecl(v_mvarId_1421_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v_userName_1431_; lean_object* v_lctx_1432_; lean_object* v_type_1433_; lean_object* v_localInstances_1434_; lean_object* v___x_1435_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v_userName_1431_ = lean_ctor_get(v_a_1430_, 0);
lean_inc(v_userName_1431_);
v_lctx_1432_ = lean_ctor_get(v_a_1430_, 1);
lean_inc_ref(v_lctx_1432_);
v_type_1433_ = lean_ctor_get(v_a_1430_, 2);
lean_inc_ref(v_type_1433_);
v_localInstances_1434_ = lean_ctor_get(v_a_1430_, 4);
lean_inc_ref(v_localInstances_1434_);
lean_dec(v_a_1430_);
v___x_1435_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_1432_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = l_Lean_Meta_Sym_preprocessExpr(v_type_1433_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; uint8_t v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = 2;
v___x_1440_ = lean_unsigned_to_nat(0u);
v___x_1441_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_1436_, v_localInstances_1434_, v_a_1438_, v___x_1439_, v_userName_1431_, v___x_1440_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1451_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc_n(v_a_1442_, 2);
lean_dec_ref_known(v___x_1441_, 1);
v___x_1443_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1421_, v_a_1442_, v_a_1425_);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; 
v_unused_1452_ = lean_ctor_get(v___x_1443_, 0);
lean_dec(v_unused_1452_);
v___x_1445_ = v___x_1443_;
v_isShared_1446_ = v_isSharedCheck_1451_;
goto v_resetjp_1444_;
}
else
{
lean_dec(v___x_1443_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1451_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1447_ = l_Lean_Expr_mvarId_x21(v_a_1442_);
lean_dec(v_a_1442_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1447_);
v___x_1449_ = v___x_1445_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_mvarId_1421_);
v_a_1453_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1441_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1441_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec(v_a_1436_);
lean_dec_ref(v_localInstances_1434_);
lean_dec(v_userName_1431_);
lean_dec(v_mvarId_1421_);
v_a_1461_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1437_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1437_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref(v_localInstances_1434_);
lean_dec_ref(v_type_1433_);
lean_dec(v_userName_1431_);
lean_dec(v_mvarId_1421_);
v_a_1469_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1435_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1435_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec(v_mvarId_1421_);
v_a_1477_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1429_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1429_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar___boxed(lean_object* v_mvarId_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(lean_object* v_mvarId_1494_, lean_object* v_val_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1494_, v_val_1495_, v___y_1499_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___boxed(lean_object* v_mvarId_1504_, lean_object* v_val_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(v_mvarId_1504_, v_val_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0(lean_object* v_00_u03b2_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_x_1515_, v_x_1516_, v_x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1519_, lean_object* v_x_1520_, size_t v_x_1521_, size_t v_x_1522_, lean_object* v_x_1523_, lean_object* v_x_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1520_, v_x_1521_, v_x_1522_, v_x_1523_, v_x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_){
_start:
{
size_t v_x_2604__boxed_1532_; size_t v_x_2605__boxed_1533_; lean_object* v_res_1534_; 
v_x_2604__boxed_1532_ = lean_unbox_usize(v_x_1528_);
lean_dec(v_x_1528_);
v_x_2605__boxed_1533_ = lean_unbox_usize(v_x_1529_);
lean_dec(v_x_1529_);
v_res_1534_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(v_00_u03b2_1526_, v_x_1527_, v_x_2604__boxed_1532_, v_x_2605__boxed_1533_, v_x_1530_, v_x_1531_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1535_, lean_object* v_n_1536_, lean_object* v_k_1537_, lean_object* v_v_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1536_, v_k_1537_, v_v_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1540_, size_t v_depth_1541_, lean_object* v_keys_1542_, lean_object* v_vals_1543_, lean_object* v_heq_1544_, lean_object* v_i_1545_, lean_object* v_entries_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1541_, v_keys_1542_, v_vals_1543_, v_i_1545_, v_entries_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1548_, lean_object* v_depth_1549_, lean_object* v_keys_1550_, lean_object* v_vals_1551_, lean_object* v_heq_1552_, lean_object* v_i_1553_, lean_object* v_entries_1554_){
_start:
{
size_t v_depth_boxed_1555_; lean_object* v_res_1556_; 
v_depth_boxed_1555_ = lean_unbox_usize(v_depth_1549_);
lean_dec(v_depth_1549_);
v_res_1556_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1548_, v_depth_boxed_1555_, v_keys_1550_, v_vals_1551_, v_heq_1552_, v_i_1553_, v_entries_1554_);
lean_dec_ref(v_vals_1551_);
lean_dec_ref(v_keys_1550_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1557_, lean_object* v_x_1558_, lean_object* v_x_1559_, lean_object* v_x_1560_, lean_object* v_x_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1558_, v_x_1559_, v_x_1560_, v_x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(lean_object* v_msgData_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; lean_object* v_env_1570_; uint8_t v___x_1571_; lean_object* v_env_1572_; lean_object* v___x_1573_; lean_object* v_toCold_1574_; lean_object* v_mctx_1575_; lean_object* v_lctx_1576_; lean_object* v_options_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1569_ = lean_st_ref_get(v___y_1567_);
v_env_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc_ref(v_env_1570_);
lean_dec(v___x_1569_);
v___x_1571_ = 0;
v_env_1572_ = l_Lean_Environment_setRecordingDeps(v_env_1570_, v___x_1571_);
v___x_1573_ = lean_st_ref_get(v___y_1565_);
v_toCold_1574_ = lean_ctor_get(v___y_1566_, 0);
v_mctx_1575_ = lean_ctor_get(v___x_1573_, 0);
lean_inc_ref(v_mctx_1575_);
lean_dec(v___x_1573_);
v_lctx_1576_ = lean_ctor_get(v___y_1564_, 2);
v_options_1577_ = lean_ctor_get(v_toCold_1574_, 2);
lean_inc_ref(v_options_1577_);
lean_inc_ref(v_lctx_1576_);
v___x_1578_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1578_, 0, v_env_1572_);
lean_ctor_set(v___x_1578_, 1, v_mctx_1575_);
lean_ctor_set(v___x_1578_, 2, v_lctx_1576_);
lean_ctor_set(v___x_1578_, 3, v_options_1577_);
v___x_1579_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v_msgData_1563_);
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0___boxed(lean_object* v_msgData_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msgData_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(lean_object* v_msg_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_ref_1594_; lean_object* v___x_1595_; lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1604_; 
v_ref_1594_ = lean_ctor_get(v___y_1591_, 2);
v___x_1595_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msg_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
lean_inc(v_ref_1594_);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v_ref_1594_);
lean_ctor_set(v___x_1600_, 1, v_a_1596_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set_tag(v___x_1598_, 1);
lean_ctor_set(v___x_1598_, 0, v___x_1600_);
v___x_1602_ = v___x_1598_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(lean_object* v_msg_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
return v_res_1611_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0));
v___x_1614_ = l_Lean_stringToMessageData(v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(lean_object* v_msg_1618_, lean_object* v_e_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v___y_1628_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2));
v___x_1636_ = lean_string_dec_eq(v_msg_1618_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1637_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3));
v___x_1638_ = lean_string_append(v___x_1637_, v_msg_1618_);
lean_dec_ref(v_msg_1618_);
v___x_1639_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4));
v___x_1640_ = lean_string_append(v___x_1638_, v___x_1639_);
v___y_1628_ = v___x_1640_;
goto v___jp_1627_;
}
else
{
v___y_1628_ = v_msg_1618_;
goto v___jp_1627_;
}
v___jp_1627_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1629_ = l_Lean_stringToMessageData(v___y_1628_);
v___x_1630_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = l_Lean_indentExpr(v_e_1619_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v___x_1633_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
return v___x_1634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(lean_object* v_msg_1641_, lean_object* v_e_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1641_, v_e_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_object* v_00_u03b1_1651_, lean_object* v_msg_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_1652_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(lean_object* v_00_u03b1_1661_, lean_object* v_msg_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(v_00_u03b1_1661_, v_msg_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1671_, lean_object* v_vals_1672_, lean_object* v_i_1673_, lean_object* v_k_1674_){
_start:
{
lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1675_ = lean_array_get_size(v_keys_1671_);
v___x_1676_ = lean_nat_dec_lt(v_i_1673_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; 
lean_dec(v_i_1673_);
v___x_1677_ = lean_box(0);
return v___x_1677_;
}
else
{
lean_object* v_k_x27_1678_; uint8_t v___x_1679_; 
v_k_x27_1678_ = lean_array_fget_borrowed(v_keys_1671_, v_i_1673_);
v___x_1679_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_1674_, v_k_x27_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_unsigned_to_nat(1u);
v___x_1681_ = lean_nat_add(v_i_1673_, v___x_1680_);
lean_dec(v_i_1673_);
v_i_1673_ = v___x_1681_;
goto _start;
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = lean_array_fget_borrowed(v_vals_1672_, v_i_1673_);
lean_dec(v_i_1673_);
lean_inc(v___x_1683_);
lean_inc(v_k_x27_1678_);
v___x_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1684_, 0, v_k_x27_1678_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
return v___x_1685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1686_, lean_object* v_vals_1687_, lean_object* v_i_1688_, lean_object* v_k_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_1686_, v_vals_1687_, v_i_1688_, v_k_1689_);
lean_dec_ref(v_k_1689_);
lean_dec_ref(v_vals_1687_);
lean_dec_ref(v_keys_1686_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(lean_object* v_x_1691_, size_t v_x_1692_, lean_object* v_x_1693_){
_start:
{
if (lean_obj_tag(v_x_1691_) == 0)
{
lean_object* v_es_1694_; lean_object* v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; lean_object* v_j_1698_; lean_object* v___x_1699_; 
v_es_1694_ = lean_ctor_get(v_x_1691_, 0);
v___x_1695_ = lean_box(2);
v___x_1696_ = ((size_t)31ULL);
v___x_1697_ = lean_usize_land(v_x_1692_, v___x_1696_);
v_j_1698_ = lean_usize_to_nat(v___x_1697_);
v___x_1699_ = lean_array_get_borrowed(v___x_1695_, v_es_1694_, v_j_1698_);
lean_dec(v_j_1698_);
switch(lean_obj_tag(v___x_1699_))
{
case 0:
{
lean_object* v_key_1700_; lean_object* v_val_1701_; uint8_t v___x_1702_; 
v_key_1700_ = lean_ctor_get(v___x_1699_, 0);
v_val_1701_ = lean_ctor_get(v___x_1699_, 1);
v___x_1702_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_1693_, v_key_1700_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_box(0);
return v___x_1703_;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_inc(v_val_1701_);
lean_inc(v_key_1700_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v_key_1700_);
lean_ctor_set(v___x_1704_, 1, v_val_1701_);
v___x_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
return v___x_1705_;
}
}
case 1:
{
lean_object* v_node_1706_; size_t v___x_1707_; size_t v___x_1708_; 
v_node_1706_ = lean_ctor_get(v___x_1699_, 0);
v___x_1707_ = ((size_t)5ULL);
v___x_1708_ = lean_usize_shift_right(v_x_1692_, v___x_1707_);
v_x_1691_ = v_node_1706_;
v_x_1692_ = v___x_1708_;
goto _start;
}
default: 
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_box(0);
return v___x_1710_;
}
}
}
else
{
lean_object* v_ks_1711_; lean_object* v_vs_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_ks_1711_ = lean_ctor_get(v_x_1691_, 0);
v_vs_1712_ = lean_ctor_get(v_x_1691_, 1);
v___x_1713_ = lean_unsigned_to_nat(0u);
v___x_1714_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_ks_1711_, v_vs_1712_, v___x_1713_, v_x_1693_);
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_){
_start:
{
size_t v_x_7386__boxed_1718_; lean_object* v_res_1719_; 
v_x_7386__boxed_1718_ = lean_unbox_usize(v_x_1716_);
lean_dec(v_x_1716_);
v_res_1719_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_1715_, v_x_7386__boxed_1718_, v_x_1717_);
lean_dec_ref(v_x_1717_);
lean_dec_ref(v_x_1715_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(lean_object* v_x_1720_, lean_object* v_x_1721_){
_start:
{
uint64_t v___x_1722_; size_t v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_1721_);
v___x_1723_ = lean_uint64_to_usize(v___x_1722_);
v___x_1724_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_1720_, v___x_1723_, v_x_1721_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg___boxed(lean_object* v_x_1725_, lean_object* v_x_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_1725_, v_x_1726_);
lean_dec_ref(v_x_1726_);
lean_dec_ref(v_x_1725_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0(lean_object* v_msg_1728_, lean_object* v_e_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___y_1742_; lean_object* v___x_1751_; lean_object* v_share_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_st_ref_get(v___y_1731_);
v_share_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc_ref(v_share_1752_);
lean_dec(v___x_1751_);
v___x_1753_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_share_1752_, v_e_1729_);
lean_dec_ref(v_share_1752_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1728_, v_e_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
v___y_1742_ = v___x_1754_;
goto v___jp_1741_;
}
else
{
lean_object* v_val_1755_; lean_object* v_fst_1756_; size_t v___x_1757_; size_t v___x_1758_; uint8_t v___x_1759_; 
v_val_1755_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_val_1755_);
lean_dec_ref_known(v___x_1753_, 1);
v_fst_1756_ = lean_ctor_get(v_val_1755_, 0);
lean_inc(v_fst_1756_);
lean_dec(v_val_1755_);
v___x_1757_ = lean_ptr_addr(v_fst_1756_);
lean_dec(v_fst_1756_);
v___x_1758_ = lean_ptr_addr(v_e_1729_);
v___x_1759_ = lean_usize_dec_eq(v___x_1757_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
v___x_1760_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1728_, v_e_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
v___y_1742_ = v___x_1760_;
goto v___jp_1741_;
}
else
{
lean_dec_ref(v_e_1729_);
lean_dec_ref(v_msg_1728_);
goto v___jp_1737_;
}
}
v___jp_1737_:
{
uint8_t v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = 1;
v___x_1739_ = lean_box(v___x_1738_);
v___x_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
return v___x_1740_;
}
v___jp_1741_:
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
v_a_1743_ = lean_ctor_get(v___y_1742_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___y_1742_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___y_1742_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___y_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0___boxed(lean_object* v_msg_1761_, lean_object* v_e_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Expr_checkMaxShared___lam__0(v_msg_1761_, v_e_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(lean_object* v_a_1771_, lean_object* v_x_1772_){
_start:
{
if (lean_obj_tag(v_x_1772_) == 0)
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_box(0);
return v___x_1773_;
}
else
{
lean_object* v_key_1774_; lean_object* v_value_1775_; lean_object* v_tail_1776_; uint8_t v___x_1777_; 
v_key_1774_ = lean_ctor_get(v_x_1772_, 0);
v_value_1775_ = lean_ctor_get(v_x_1772_, 1);
v_tail_1776_ = lean_ctor_get(v_x_1772_, 2);
v___x_1777_ = lean_expr_eqv(v_key_1774_, v_a_1771_);
if (v___x_1777_ == 0)
{
v_x_1772_ = v_tail_1776_;
goto _start;
}
else
{
lean_object* v___x_1779_; 
lean_inc(v_value_1775_);
v___x_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1779_, 0, v_value_1775_);
return v___x_1779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_1780_, lean_object* v_x_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_1780_, v_x_1781_);
lean_dec(v_x_1781_);
lean_dec_ref(v_a_1780_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(lean_object* v_m_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_buckets_1785_; lean_object* v___x_1786_; uint64_t v___x_1787_; uint64_t v___x_1788_; uint64_t v___x_1789_; uint64_t v_fold_1790_; uint64_t v___x_1791_; uint64_t v___x_1792_; uint64_t v___x_1793_; size_t v___x_1794_; size_t v___x_1795_; size_t v___x_1796_; size_t v___x_1797_; size_t v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_buckets_1785_ = lean_ctor_get(v_m_1783_, 1);
v___x_1786_ = lean_array_get_size(v_buckets_1785_);
v___x_1787_ = l_Lean_Expr_hash(v_a_1784_);
v___x_1788_ = 32ULL;
v___x_1789_ = lean_uint64_shift_right(v___x_1787_, v___x_1788_);
v_fold_1790_ = lean_uint64_xor(v___x_1787_, v___x_1789_);
v___x_1791_ = 16ULL;
v___x_1792_ = lean_uint64_shift_right(v_fold_1790_, v___x_1791_);
v___x_1793_ = lean_uint64_xor(v_fold_1790_, v___x_1792_);
v___x_1794_ = lean_uint64_to_usize(v___x_1793_);
v___x_1795_ = lean_usize_of_nat(v___x_1786_);
v___x_1796_ = ((size_t)1ULL);
v___x_1797_ = lean_usize_sub(v___x_1795_, v___x_1796_);
v___x_1798_ = lean_usize_land(v___x_1794_, v___x_1797_);
v___x_1799_ = lean_array_uget_borrowed(v_buckets_1785_, v___x_1798_);
v___x_1800_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_1784_, v___x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(lean_object* v_m_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_1801_, v_a_1802_);
lean_dec_ref(v_a_1802_);
lean_dec_ref(v_m_1801_);
return v_res_1803_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(lean_object* v_a_1804_, lean_object* v_x_1805_){
_start:
{
if (lean_obj_tag(v_x_1805_) == 0)
{
uint8_t v___x_1806_; 
v___x_1806_ = 0;
return v___x_1806_;
}
else
{
lean_object* v_key_1807_; lean_object* v_tail_1808_; uint8_t v___x_1809_; 
v_key_1807_ = lean_ctor_get(v_x_1805_, 0);
v_tail_1808_ = lean_ctor_get(v_x_1805_, 2);
v___x_1809_ = lean_expr_eqv(v_key_1807_, v_a_1804_);
if (v___x_1809_ == 0)
{
v_x_1805_ = v_tail_1808_;
goto _start;
}
else
{
return v___x_1809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_a_1811_, lean_object* v_x_1812_){
_start:
{
uint8_t v_res_1813_; lean_object* v_r_1814_; 
v_res_1813_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_1811_, v_x_1812_);
lean_dec(v_x_1812_);
lean_dec_ref(v_a_1811_);
v_r_1814_ = lean_box(v_res_1813_);
return v_r_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(lean_object* v_a_1815_, lean_object* v_b_1816_, lean_object* v_x_1817_){
_start:
{
if (lean_obj_tag(v_x_1817_) == 0)
{
lean_dec(v_b_1816_);
lean_dec_ref(v_a_1815_);
return v_x_1817_;
}
else
{
lean_object* v_key_1818_; lean_object* v_value_1819_; lean_object* v_tail_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1832_; 
v_key_1818_ = lean_ctor_get(v_x_1817_, 0);
v_value_1819_ = lean_ctor_get(v_x_1817_, 1);
v_tail_1820_ = lean_ctor_get(v_x_1817_, 2);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_x_1817_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1822_ = v_x_1817_;
v_isShared_1823_ = v_isSharedCheck_1832_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_tail_1820_);
lean_inc(v_value_1819_);
lean_inc(v_key_1818_);
lean_dec(v_x_1817_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1832_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
uint8_t v___x_1824_; 
v___x_1824_ = lean_expr_eqv(v_key_1818_, v_a_1815_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1825_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_1815_, v_b_1816_, v_tail_1820_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 2, v___x_1825_);
v___x_1827_ = v___x_1822_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_key_1818_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_value_1819_);
lean_ctor_set(v_reuseFailAlloc_1828_, 2, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
else
{
lean_object* v___x_1830_; 
lean_dec(v_value_1819_);
lean_dec(v_key_1818_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 1, v_b_1816_);
lean_ctor_set(v___x_1822_, 0, v_a_1815_);
v___x_1830_ = v___x_1822_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1815_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_b_1816_);
lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_tail_1820_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(lean_object* v_x_1833_, lean_object* v_x_1834_){
_start:
{
if (lean_obj_tag(v_x_1834_) == 0)
{
return v_x_1833_;
}
else
{
lean_object* v_key_1835_; lean_object* v_value_1836_; lean_object* v_tail_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1860_; 
v_key_1835_ = lean_ctor_get(v_x_1834_, 0);
v_value_1836_ = lean_ctor_get(v_x_1834_, 1);
v_tail_1837_ = lean_ctor_get(v_x_1834_, 2);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_x_1834_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1839_ = v_x_1834_;
v_isShared_1840_ = v_isSharedCheck_1860_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_tail_1837_);
lean_inc(v_value_1836_);
lean_inc(v_key_1835_);
lean_dec(v_x_1834_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1860_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; uint64_t v___x_1842_; uint64_t v___x_1843_; uint64_t v___x_1844_; uint64_t v_fold_1845_; uint64_t v___x_1846_; uint64_t v___x_1847_; uint64_t v___x_1848_; size_t v___x_1849_; size_t v___x_1850_; size_t v___x_1851_; size_t v___x_1852_; size_t v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1841_ = lean_array_get_size(v_x_1833_);
v___x_1842_ = l_Lean_Expr_hash(v_key_1835_);
v___x_1843_ = 32ULL;
v___x_1844_ = lean_uint64_shift_right(v___x_1842_, v___x_1843_);
v_fold_1845_ = lean_uint64_xor(v___x_1842_, v___x_1844_);
v___x_1846_ = 16ULL;
v___x_1847_ = lean_uint64_shift_right(v_fold_1845_, v___x_1846_);
v___x_1848_ = lean_uint64_xor(v_fold_1845_, v___x_1847_);
v___x_1849_ = lean_uint64_to_usize(v___x_1848_);
v___x_1850_ = lean_usize_of_nat(v___x_1841_);
v___x_1851_ = ((size_t)1ULL);
v___x_1852_ = lean_usize_sub(v___x_1850_, v___x_1851_);
v___x_1853_ = lean_usize_land(v___x_1849_, v___x_1852_);
v___x_1854_ = lean_array_uget_borrowed(v_x_1833_, v___x_1853_);
lean_inc(v___x_1854_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 2, v___x_1854_);
v___x_1856_ = v___x_1839_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_key_1835_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_value_1836_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_array_uset(v_x_1833_, v___x_1853_, v___x_1856_);
v_x_1833_ = v___x_1857_;
v_x_1834_ = v_tail_1837_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(lean_object* v_i_1861_, lean_object* v_source_1862_, lean_object* v_target_1863_){
_start:
{
lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = lean_array_get_size(v_source_1862_);
v___x_1865_ = lean_nat_dec_lt(v_i_1861_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_dec_ref(v_source_1862_);
lean_dec(v_i_1861_);
return v_target_1863_;
}
else
{
lean_object* v_es_1866_; lean_object* v___x_1867_; lean_object* v_source_1868_; lean_object* v_target_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v_es_1866_ = lean_array_fget(v_source_1862_, v_i_1861_);
v___x_1867_ = lean_box(0);
v_source_1868_ = lean_array_fset(v_source_1862_, v_i_1861_, v___x_1867_);
v_target_1869_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_target_1863_, v_es_1866_);
v___x_1870_ = lean_unsigned_to_nat(1u);
v___x_1871_ = lean_nat_add(v_i_1861_, v___x_1870_);
lean_dec(v_i_1861_);
v_i_1861_ = v___x_1871_;
v_source_1862_ = v_source_1868_;
v_target_1863_ = v_target_1869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(lean_object* v_data_1873_){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v_nbuckets_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1874_ = lean_array_get_size(v_data_1873_);
v___x_1875_ = lean_unsigned_to_nat(2u);
v_nbuckets_1876_ = lean_nat_mul(v___x_1874_, v___x_1875_);
v___x_1877_ = lean_unsigned_to_nat(0u);
v___x_1878_ = lean_box(0);
v___x_1879_ = lean_mk_array(v_nbuckets_1876_, v___x_1878_);
v___x_1880_ = lean_array_propagate_mark(v_data_1873_, v___x_1879_);
v___x_1881_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v___x_1877_, v_data_1873_, v___x_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(lean_object* v_m_1882_, lean_object* v_a_1883_, lean_object* v_b_1884_){
_start:
{
lean_object* v_size_1885_; lean_object* v_buckets_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1929_; 
v_size_1885_ = lean_ctor_get(v_m_1882_, 0);
v_buckets_1886_ = lean_ctor_get(v_m_1882_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_m_1882_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1888_ = v_m_1882_;
v_isShared_1889_ = v_isSharedCheck_1929_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_buckets_1886_);
lean_inc(v_size_1885_);
lean_dec(v_m_1882_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1929_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; uint64_t v___x_1891_; uint64_t v___x_1892_; uint64_t v___x_1893_; uint64_t v_fold_1894_; uint64_t v___x_1895_; uint64_t v___x_1896_; uint64_t v___x_1897_; size_t v___x_1898_; size_t v___x_1899_; size_t v___x_1900_; size_t v___x_1901_; size_t v___x_1902_; lean_object* v_bkt_1903_; uint8_t v___x_1904_; 
v___x_1890_ = lean_array_get_size(v_buckets_1886_);
v___x_1891_ = l_Lean_Expr_hash(v_a_1883_);
v___x_1892_ = 32ULL;
v___x_1893_ = lean_uint64_shift_right(v___x_1891_, v___x_1892_);
v_fold_1894_ = lean_uint64_xor(v___x_1891_, v___x_1893_);
v___x_1895_ = 16ULL;
v___x_1896_ = lean_uint64_shift_right(v_fold_1894_, v___x_1895_);
v___x_1897_ = lean_uint64_xor(v_fold_1894_, v___x_1896_);
v___x_1898_ = lean_uint64_to_usize(v___x_1897_);
v___x_1899_ = lean_usize_of_nat(v___x_1890_);
v___x_1900_ = ((size_t)1ULL);
v___x_1901_ = lean_usize_sub(v___x_1899_, v___x_1900_);
v___x_1902_ = lean_usize_land(v___x_1898_, v___x_1901_);
v_bkt_1903_ = lean_array_uget_borrowed(v_buckets_1886_, v___x_1902_);
v___x_1904_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_1883_, v_bkt_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v_size_x27_1906_; lean_object* v___x_1907_; lean_object* v_buckets_x27_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1905_ = lean_unsigned_to_nat(1u);
v_size_x27_1906_ = lean_nat_add(v_size_1885_, v___x_1905_);
lean_dec(v_size_1885_);
lean_inc(v_bkt_1903_);
v___x_1907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1907_, 0, v_a_1883_);
lean_ctor_set(v___x_1907_, 1, v_b_1884_);
lean_ctor_set(v___x_1907_, 2, v_bkt_1903_);
v_buckets_x27_1908_ = lean_array_uset(v_buckets_1886_, v___x_1902_, v___x_1907_);
v___x_1909_ = lean_unsigned_to_nat(4u);
v___x_1910_ = lean_nat_mul(v_size_x27_1906_, v___x_1909_);
v___x_1911_ = lean_unsigned_to_nat(3u);
v___x_1912_ = lean_nat_div(v___x_1910_, v___x_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_array_get_size(v_buckets_x27_1908_);
v___x_1914_ = lean_nat_dec_le(v___x_1912_, v___x_1913_);
lean_dec(v___x_1912_);
if (v___x_1914_ == 0)
{
lean_object* v_val_1915_; lean_object* v___x_1917_; 
v_val_1915_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_buckets_x27_1908_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v_val_1915_);
lean_ctor_set(v___x_1888_, 0, v_size_x27_1906_);
v___x_1917_ = v___x_1888_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_size_x27_1906_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_val_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
else
{
lean_object* v___x_1920_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v_buckets_x27_1908_);
lean_ctor_set(v___x_1888_, 0, v_size_x27_1906_);
v___x_1920_ = v___x_1888_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_size_x27_1906_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_buckets_x27_1908_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
else
{
lean_object* v___x_1922_; lean_object* v_buckets_x27_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
lean_inc(v_bkt_1903_);
v___x_1922_ = lean_box(0);
v_buckets_x27_1923_ = lean_array_uset(v_buckets_1886_, v___x_1902_, v___x_1922_);
v___x_1924_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_1883_, v_b_1884_, v_bkt_1903_);
v___x_1925_ = lean_array_uset(v_buckets_x27_1923_, v___x_1902_, v___x_1924_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v___x_1925_);
v___x_1927_ = v___x_1888_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_size_1885_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(lean_object* v_g_1930_, lean_object* v_e_1931_, lean_object* v_a_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_a_1941_; lean_object* v___y_1947_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = lean_st_ref_get(v_a_1932_);
v___x_1950_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v___x_1949_, v_e_1931_);
lean_dec(v___x_1949_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v___x_1951_; 
lean_inc_ref(v_g_1930_);
lean_inc(v___y_1938_);
lean_inc_ref(v___y_1937_);
lean_inc(v___y_1936_);
lean_inc_ref(v___y_1935_);
lean_inc(v___y_1934_);
lean_inc_ref(v___y_1933_);
lean_inc_ref(v_e_1931_);
v___x_1951_ = lean_apply_8(v_g_1930_, v_e_1931_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, lean_box(0));
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v_d_1954_; lean_object* v_b_1955_; lean_object* v___y_1956_; uint8_t v___x_1959_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1959_ = lean_unbox(v_a_1952_);
lean_dec(v_a_1952_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; 
lean_dec_ref(v_g_1930_);
v___x_1960_ = lean_box(0);
v_a_1941_ = v___x_1960_;
goto v___jp_1940_;
}
else
{
switch(lean_obj_tag(v_e_1931_))
{
case 7:
{
lean_object* v_binderType_1961_; lean_object* v_body_1962_; 
v_binderType_1961_ = lean_ctor_get(v_e_1931_, 1);
v_body_1962_ = lean_ctor_get(v_e_1931_, 2);
lean_inc_ref(v_body_1962_);
lean_inc_ref(v_binderType_1961_);
v_d_1954_ = v_binderType_1961_;
v_b_1955_ = v_body_1962_;
v___y_1956_ = v_a_1932_;
goto v___jp_1953_;
}
case 6:
{
lean_object* v_binderType_1963_; lean_object* v_body_1964_; 
v_binderType_1963_ = lean_ctor_get(v_e_1931_, 1);
v_body_1964_ = lean_ctor_get(v_e_1931_, 2);
lean_inc_ref(v_body_1964_);
lean_inc_ref(v_binderType_1963_);
v_d_1954_ = v_binderType_1963_;
v_b_1955_ = v_body_1964_;
v___y_1956_ = v_a_1932_;
goto v___jp_1953_;
}
case 8:
{
lean_object* v_type_1965_; lean_object* v_value_1966_; lean_object* v_body_1967_; lean_object* v___x_1968_; 
v_type_1965_ = lean_ctor_get(v_e_1931_, 1);
v_value_1966_ = lean_ctor_get(v_e_1931_, 2);
v_body_1967_ = lean_ctor_get(v_e_1931_, 3);
lean_inc_ref(v_type_1965_);
lean_inc_ref(v_g_1930_);
v___x_1968_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1930_, v_type_1965_, v_a_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v___x_1969_; 
lean_dec_ref_known(v___x_1968_, 1);
lean_inc_ref(v_value_1966_);
lean_inc_ref(v_g_1930_);
v___x_1969_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1930_, v_value_1966_, v_a_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v___x_1970_; 
lean_dec_ref_known(v___x_1969_, 1);
lean_inc_ref(v_body_1967_);
v___x_1970_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1930_, v_body_1967_, v_a_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
v___y_1947_ = v___x_1970_;
goto v___jp_1946_;
}
else
{
lean_dec_ref_known(v_e_1931_, 4);
lean_dec_ref(v_g_1930_);
return v___x_1969_;
}
}
else
{
lean_dec_ref_known(v_e_1931_, 4);
lean_dec_ref(v_g_1930_);
return v___x_1968_;
}
}
case 5:
{
lean_object* v_fn_1971_; lean_object* v_arg_1972_; lean_object* v___x_1973_; 
v_fn_1971_ = lean_ctor_get(v_e_1931_, 0);
v_arg_1972_ = lean_ctor_get(v_e_1931_, 1);
lean_inc_ref(v_fn_1971_);
lean_inc_ref(v_g_1930_);
v___x_1973_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1930_, v_fn_1971_, v_a_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v___x_1974_; 
lean_dec_ref_known(v___x_1973_, 1);
lean_inc_ref(v_arg_1972_);
v___x_1974_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1930_, v_arg_1972_, v_a_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
v___y_1947_ = v___x_1974_;
goto v___jp_1946_;
}
else
{
lean_dec_ref_known(v_e_1931_, 2);
lean_dec_ref(v_g_1930_);
return v___x_1973_;
}
}
case 10:
{
lean_object* v_expr_1975_; lean_object* v___x_1976_; 
v_expr_1975_ = lean_ctor_get(v_e_1931_, 1);
lean_inc_ref(v_expr_1975_);
v___x_1976_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1930_, v_expr_1975_, v_a_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
v___y_1947_ = v___x_1976_;
goto v___jp_1946_;
}
case 11:
{
lean_object* v_struct_1977_; lean_object* v___x_1978_; 
v_struct_1977_ = lean_ctor_get(v_e_1931_, 2);
lean_inc_ref(v_struct_1977_);
v___x_1978_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1930_, v_struct_1977_, v_a_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
v___y_1947_ = v___x_1978_;
goto v___jp_1946_;
}
default: 
{
lean_object* v___x_1979_; 
lean_dec_ref(v_g_1930_);
v___x_1979_ = lean_box(0);
v_a_1941_ = v___x_1979_;
goto v___jp_1940_;
}
}
}
v___jp_1953_:
{
lean_object* v___x_1957_; 
lean_inc_ref(v_g_1930_);
v___x_1957_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1930_, v_d_1954_, v___y_1956_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v___x_1958_; 
lean_dec_ref_known(v___x_1957_, 1);
v___x_1958_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1930_, v_b_1955_, v___y_1956_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
v___y_1947_ = v___x_1958_;
goto v___jp_1946_;
}
else
{
lean_dec_ref(v_b_1955_);
lean_dec_ref(v_e_1931_);
lean_dec_ref(v_g_1930_);
return v___x_1957_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v_e_1931_);
lean_dec_ref(v_g_1930_);
v_a_1980_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1951_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1951_);
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
lean_object* v_val_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v_e_1931_);
lean_dec_ref(v_g_1930_);
v_val_1988_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1950_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_val_1988_);
lean_dec(v___x_1950_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set_tag(v___x_1990_, 0);
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_val_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
v___jp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1942_ = lean_st_ref_take(v_a_1932_);
v___x_1943_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v___x_1942_, v_e_1931_, v_a_1941_);
v___x_1944_ = lean_st_ref_put(v_a_1932_, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1945_, 0, v_a_1941_);
return v___x_1945_;
}
v___jp_1946_:
{
if (lean_obj_tag(v___y_1947_) == 0)
{
lean_object* v_a_1948_; 
v_a_1948_ = lean_ctor_get(v___y_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___y_1947_, 1);
v_a_1941_ = v_a_1948_;
goto v___jp_1940_;
}
else
{
lean_dec_ref(v_e_1931_);
return v___y_1947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(lean_object* v_g_1996_, lean_object* v_e_1997_, lean_object* v_a_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1996_, v_e_1997_, v_a_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v_a_1998_);
return v_res_2006_;
}
}
static lean_object* _init_l_Lean_Expr_checkMaxShared___closed__0(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_unsigned_to_nat(16u);
v___x_2009_ = lean_mk_array(v___x_2008_, v___x_2007_);
return v___x_2009_;
}
}
static lean_object* _init_l_Lean_Expr_checkMaxShared___closed__1(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__0, &l_Lean_Expr_checkMaxShared___closed__0_once, _init_l_Lean_Expr_checkMaxShared___closed__0);
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
lean_ctor_set(v___x_2012_, 1, v___x_2010_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared(lean_object* v_e_2013_, lean_object* v_msg_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___f_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___f_2022_ = lean_alloc_closure((void*)(l_Lean_Expr_checkMaxShared___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2022_, 0, v_msg_2014_);
v___x_2023_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__1, &l_Lean_Expr_checkMaxShared___closed__1_once, _init_l_Lean_Expr_checkMaxShared___closed__1);
v___x_2024_ = lean_st_mk_ref(v___x_2023_);
v___x_2025_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v___f_2022_, v_e_2013_, v___x_2024_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2034_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2034_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2034_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2030_ = lean_st_ref_get(v___x_2024_);
lean_dec(v___x_2024_);
lean_dec(v___x_2030_);
if (v_isShared_2029_ == 0)
{
v___x_2032_ = v___x_2028_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2026_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
else
{
lean_dec(v___x_2024_);
return v___x_2025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___boxed(lean_object* v_e_2035_, lean_object* v_msg_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_Expr_checkMaxShared(v_e_2035_, v_msg_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(lean_object* v_00_u03b2_2045_, lean_object* v_x_2046_, lean_object* v_x_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_2046_, v_x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___boxed(lean_object* v_00_u03b2_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(v_00_u03b2_2049_, v_x_2050_, v_x_2051_);
lean_dec_ref(v_x_2051_);
lean_dec_ref(v_x_2050_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_object* v_00_u03b2_2053_, lean_object* v_x_2054_, size_t v_x_2055_, lean_object* v_x_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_2054_, v_x_2055_, v_x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2058_, lean_object* v_x_2059_, lean_object* v_x_2060_, lean_object* v_x_2061_){
_start:
{
size_t v_x_7973__boxed_2062_; lean_object* v_res_2063_; 
v_x_7973__boxed_2062_ = lean_unbox_usize(v_x_2060_);
lean_dec(v_x_2060_);
v_res_2063_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(v_00_u03b2_2058_, v_x_2059_, v_x_7973__boxed_2062_, v_x_2061_);
lean_dec_ref(v_x_2061_);
lean_dec_ref(v_x_2059_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(lean_object* v_00_u03b2_2064_, lean_object* v_m_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_2065_, v_a_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2068_, lean_object* v_m_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(v_00_u03b2_2068_, v_m_2069_, v_a_2070_);
lean_dec_ref(v_a_2070_);
lean_dec_ref(v_m_2069_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(lean_object* v_00_u03b2_2072_, lean_object* v_m_2073_, lean_object* v_a_2074_, lean_object* v_b_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_m_2073_, v_a_2074_, v_b_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2077_, lean_object* v_keys_2078_, lean_object* v_vals_2079_, lean_object* v_heq_2080_, lean_object* v_i_2081_, lean_object* v_k_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_2078_, v_vals_2079_, v_i_2081_, v_k_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2084_, lean_object* v_keys_2085_, lean_object* v_vals_2086_, lean_object* v_heq_2087_, lean_object* v_i_2088_, lean_object* v_k_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(v_00_u03b2_2084_, v_keys_2085_, v_vals_2086_, v_heq_2087_, v_i_2088_, v_k_2089_);
lean_dec_ref(v_k_2089_);
lean_dec_ref(v_vals_2086_);
lean_dec_ref(v_keys_2085_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2091_, lean_object* v_a_2092_, lean_object* v_x_2093_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_2092_, v_x_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2095_, lean_object* v_a_2096_, lean_object* v_x_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(v_00_u03b2_2095_, v_a_2096_, v_x_2097_);
lean_dec(v_x_2097_);
lean_dec_ref(v_a_2096_);
return v_res_2098_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2099_, lean_object* v_a_2100_, lean_object* v_x_2101_){
_start:
{
uint8_t v___x_2102_; 
v___x_2102_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_2100_, v_x_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2103_, lean_object* v_a_2104_, lean_object* v_x_2105_){
_start:
{
uint8_t v_res_2106_; lean_object* v_r_2107_; 
v_res_2106_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(v_00_u03b2_2103_, v_a_2104_, v_x_2105_);
lean_dec(v_x_2105_);
lean_dec_ref(v_a_2104_);
v_r_2107_ = lean_box(v_res_2106_);
return v_r_2107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2108_, lean_object* v_data_2109_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_data_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2111_, lean_object* v_a_2112_, lean_object* v_b_2113_, lean_object* v_x_2114_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_2112_, v_b_2113_, v_x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_2116_, lean_object* v_i_2117_, lean_object* v_source_2118_, lean_object* v_target_2119_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v_i_2117_, v_source_2118_, v_target_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9(lean_object* v_00_u03b2_2121_, lean_object* v_x_2122_, lean_object* v_x_2123_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_x_2122_, v_x_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared(lean_object* v_mvarId_2125_, lean_object* v_msg_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_MVarId_getDecl(v_mvarId_2125_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v_type_2136_; lean_object* v___x_2137_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v_type_2136_ = lean_ctor_get(v_a_2135_, 2);
lean_inc_ref(v_type_2136_);
lean_dec(v_a_2135_);
v___x_2137_ = l_Lean_Expr_checkMaxShared(v_type_2136_, v_msg_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
return v___x_2137_;
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v_msg_2126_);
v_a_2138_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2134_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2134_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared___boxed(lean_object* v_mvarId_2146_, lean_object* v_msg_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_MVarId_checkMaxShared(v_mvarId_2146_, v_msg_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
return v_res_2155_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(lean_object* v_x_2156_){
_start:
{
if (lean_obj_tag(v_x_2156_) == 0)
{
uint8_t v___x_2157_; 
v___x_2157_ = 0;
return v___x_2157_;
}
else
{
lean_object* v_head_2158_; lean_object* v_tail_2159_; uint8_t v___x_2160_; 
v_head_2158_ = lean_ctor_get(v_x_2156_, 0);
v_tail_2159_ = lean_ctor_get(v_x_2156_, 1);
v___x_2160_ = l_Lean_Level_isAlreadyNormalizedCheap(v_head_2158_);
if (v___x_2160_ == 0)
{
uint8_t v___x_2161_; 
v___x_2161_ = 1;
return v___x_2161_;
}
else
{
v_x_2156_ = v_tail_2159_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0___boxed(lean_object* v_x_2163_){
_start:
{
uint8_t v_res_2164_; lean_object* v_r_2165_; 
v_res_2164_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_x_2163_);
lean_dec(v_x_2163_);
v_r_2165_ = lean_box(v_res_2164_);
return v_r_2165_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(lean_object* v_x_2166_){
_start:
{
switch(lean_obj_tag(v_x_2166_))
{
case 4:
{
lean_object* v_us_2167_; uint8_t v___x_2168_; 
v_us_2167_ = lean_ctor_get(v_x_2166_, 1);
v___x_2168_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_us_2167_);
return v___x_2168_;
}
case 3:
{
lean_object* v_u_2169_; uint8_t v___x_2170_; 
v_u_2169_ = lean_ctor_get(v_x_2166_, 0);
v___x_2170_ = l_Lean_Level_isAlreadyNormalizedCheap(v_u_2169_);
if (v___x_2170_ == 0)
{
uint8_t v___x_2171_; 
v___x_2171_ = 1;
return v___x_2171_;
}
else
{
uint8_t v___x_2172_; 
v___x_2172_ = 0;
return v___x_2172_;
}
}
default: 
{
uint8_t v___x_2173_; 
v___x_2173_ = 0;
return v___x_2173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(lean_object* v_x_2174_){
_start:
{
uint8_t v_res_2175_; lean_object* v_r_2176_; 
v_res_2175_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(v_x_2174_);
lean_dec_ref(v_x_2174_);
v_r_2176_ = lean_box(v_res_2175_);
return v_r_2176_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(lean_object* v_e_2178_){
_start:
{
lean_object* v___f_2179_; lean_object* v___x_2180_; 
v___f_2179_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0));
v___x_2180_ = lean_find_expr(v___f_2179_, v_e_2178_);
if (lean_obj_tag(v___x_2180_) == 0)
{
uint8_t v___x_2181_; 
v___x_2181_ = 1;
return v___x_2181_;
}
else
{
uint8_t v___x_2182_; 
lean_dec_ref_known(v___x_2180_, 1);
v___x_2182_ = 0;
return v___x_2182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___boxed(lean_object* v_e_2183_){
_start:
{
uint8_t v_res_2184_; lean_object* v_r_2185_; 
v_res_2184_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_2183_);
lean_dec_ref(v_e_2183_);
v_r_2185_ = lean_box(v_res_2184_);
return v_r_2185_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
if (lean_obj_tag(v_a_2186_) == 0)
{
lean_object* v___x_2188_; 
v___x_2188_ = l_List_reverse___redArg(v_a_2187_);
return v___x_2188_;
}
else
{
lean_object* v_head_2189_; lean_object* v_tail_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2199_; 
v_head_2189_ = lean_ctor_get(v_a_2186_, 0);
v_tail_2190_ = lean_ctor_get(v_a_2186_, 1);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_a_2186_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2192_ = v_a_2186_;
v_isShared_2193_ = v_isSharedCheck_2199_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_tail_2190_);
lean_inc(v_head_2189_);
lean_dec(v_a_2186_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2199_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = l_Lean_Level_normalize(v_head_2189_);
lean_dec(v_head_2189_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v_a_2187_);
lean_ctor_set(v___x_2192_, 0, v___x_2194_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_a_2187_);
v___x_2196_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
v_a_2186_ = v_tail_2190_;
v_a_2187_ = v___x_2196_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0(lean_object* v_e_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___y_2207_; lean_object* v___y_2211_; 
switch(lean_obj_tag(v_e_2202_))
{
case 3:
{
lean_object* v_u_2214_; lean_object* v___x_2215_; size_t v___x_2216_; size_t v___x_2217_; uint8_t v___x_2218_; 
v_u_2214_ = lean_ctor_get(v_e_2202_, 0);
v___x_2215_ = l_Lean_Level_normalize(v_u_2214_);
v___x_2216_ = lean_ptr_addr(v_u_2214_);
v___x_2217_ = lean_ptr_addr(v___x_2215_);
v___x_2218_ = lean_usize_dec_eq(v___x_2216_, v___x_2217_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; 
lean_dec_ref_known(v_e_2202_, 1);
v___x_2219_ = l_Lean_Expr_sort___override(v___x_2215_);
v___y_2207_ = v___x_2219_;
goto v___jp_2206_;
}
else
{
lean_dec(v___x_2215_);
v___y_2207_ = v_e_2202_;
goto v___jp_2206_;
}
}
case 4:
{
lean_object* v_declName_2220_; lean_object* v_us_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v_declName_2220_ = lean_ctor_get(v_e_2202_, 0);
v_us_2221_ = lean_ctor_get(v_e_2202_, 1);
v___x_2222_ = lean_box(0);
lean_inc(v_us_2221_);
v___x_2223_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(v_us_2221_, v___x_2222_);
v___x_2224_ = l_ptrEqList___redArg(v_us_2221_, v___x_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; 
lean_inc(v_declName_2220_);
lean_dec_ref_known(v_e_2202_, 2);
v___x_2225_ = l_Lean_Expr_const___override(v_declName_2220_, v___x_2223_);
v___y_2211_ = v___x_2225_;
goto v___jp_2210_;
}
else
{
lean_dec(v___x_2223_);
v___y_2211_ = v_e_2202_;
goto v___jp_2210_;
}
}
default: 
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_dec_ref(v_e_2202_);
v___x_2226_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___lam__0___closed__0));
v___x_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
return v___x_2227_;
}
}
v___jp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___y_2207_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
v___jp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___y_2211_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed(lean_object* v_e_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_Meta_Sym_normalizeLevels___lam__0(v_e_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1(lean_object* v_e_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v_e_2233_);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed(lean_object* v_e_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Meta_Sym_normalizeLevels___lam__1(v_e_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
return v_res_2243_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = l_Lean_maxRecDepthErrorMessage;
v___x_2250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3);
v___x_2252_ = l_Lean_MessageData_ofFormat(v___x_2251_);
return v___x_2252_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4);
v___x_2254_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__2));
v___x_2255_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v___x_2253_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_ref_2256_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5);
v___x_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2259_, 0, v_ref_2256_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v___x_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_ref_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2261_);
return v_res_2263_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = lean_box(0);
v___x_2265_ = l_Lean_interruptExceptionId;
v___x_2266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
lean_ctor_set(v___x_2266_, 1, v___x_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg(){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0);
v___x_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___boxed(lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(lean_object* v_x_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v___y_2278_; uint8_t v___y_2288_; lean_object* v___y_2289_; uint16_t v___y_2290_; lean_object* v___y_2291_; uint8_t v___y_2292_; uint8_t v___y_2293_; lean_object* v___y_2294_; lean_object* v_toCold_2299_; lean_object* v_currRecDepth_2300_; lean_object* v_ref_2301_; uint16_t v_optionFlags_2302_; uint8_t v_suppressElabErrors_2303_; uint8_t v_checkDeprecated_2304_; uint8_t v_isRecordingDeps_2305_; lean_object* v_maxRecDepth_2306_; lean_object* v_cancelTk_x3f_2307_; 
v_toCold_2299_ = lean_ctor_get(v___y_2274_, 0);
v_currRecDepth_2300_ = lean_ctor_get(v___y_2274_, 1);
v_ref_2301_ = lean_ctor_get(v___y_2274_, 2);
v_optionFlags_2302_ = lean_ctor_get_uint16(v___y_2274_, sizeof(void*)*3);
v_suppressElabErrors_2303_ = lean_ctor_get_uint8(v___y_2274_, sizeof(void*)*3 + 2);
v_checkDeprecated_2304_ = lean_ctor_get_uint8(v___y_2274_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2305_ = lean_ctor_get_uint8(v___y_2274_, sizeof(void*)*3 + 4);
v_maxRecDepth_2306_ = lean_ctor_get(v_toCold_2299_, 3);
v_cancelTk_x3f_2307_ = lean_ctor_get(v_toCold_2299_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2307_) == 1)
{
lean_object* v_val_2313_; uint8_t v___x_2314_; 
v_val_2313_ = lean_ctor_get(v_cancelTk_x3f_2307_, 0);
v___x_2314_ = l_IO_CancelToken_isSet(v_val_2313_);
if (v___x_2314_ == 0)
{
goto v___jp_2308_;
}
else
{
lean_object* v___x_2315_; lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref(v_x_2272_);
v___x_2315_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
goto v___jp_2308_;
}
v___jp_2277_:
{
if (lean_obj_tag(v___y_2278_) == 0)
{
return v___y_2278_;
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
v_a_2279_ = lean_ctor_get(v___y_2278_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___y_2278_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___y_2278_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___y_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
v___jp_2287_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2295_ = lean_unsigned_to_nat(1u);
v___x_2296_ = lean_nat_add(v___y_2289_, v___x_2295_);
lean_inc_ref(v___y_2294_);
v___x_2297_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2297_, 0, v___y_2294_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
lean_ctor_set(v___x_2297_, 2, v___y_2291_);
lean_ctor_set_uint16(v___x_2297_, sizeof(void*)*3, v___y_2290_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*3 + 2, v___y_2292_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*3 + 3, v___y_2293_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*3 + 4, v___y_2288_);
lean_inc(v___y_2275_);
lean_inc(v___y_2273_);
v___x_2298_ = lean_apply_4(v_x_2272_, v___y_2273_, v___x_2297_, v___y_2275_, lean_box(0));
v___y_2278_ = v___x_2298_;
goto v___jp_2277_;
}
v___jp_2308_:
{
lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = lean_nat_dec_eq(v_maxRecDepth_2306_, v___x_2309_);
if (v___x_2310_ == 0)
{
uint8_t v___x_2311_; 
v___x_2311_ = lean_nat_dec_eq(v_currRecDepth_2300_, v_maxRecDepth_2306_);
if (v___x_2311_ == 0)
{
lean_inc(v_ref_2301_);
v___y_2288_ = v_isRecordingDeps_2305_;
v___y_2289_ = v_currRecDepth_2300_;
v___y_2290_ = v_optionFlags_2302_;
v___y_2291_ = v_ref_2301_;
v___y_2292_ = v_suppressElabErrors_2303_;
v___y_2293_ = v_checkDeprecated_2304_;
v___y_2294_ = v_toCold_2299_;
goto v___jp_2287_;
}
else
{
lean_object* v___x_2312_; 
lean_dec_ref(v_x_2272_);
lean_inc(v_ref_2301_);
v___x_2312_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2301_);
v___y_2278_ = v___x_2312_;
goto v___jp_2277_;
}
}
else
{
lean_inc(v_ref_2301_);
v___y_2288_ = v_isRecordingDeps_2305_;
v___y_2289_ = v_currRecDepth_2300_;
v___y_2290_ = v_optionFlags_2302_;
v___y_2291_ = v_ref_2301_;
v___y_2292_ = v_suppressElabErrors_2303_;
v___y_2293_ = v_checkDeprecated_2304_;
v___y_2294_ = v_toCold_2299_;
goto v___jp_2287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_x_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v_x_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(lean_object* v_x_2330_, lean_object* v_x_2331_){
_start:
{
if (lean_obj_tag(v_x_2331_) == 0)
{
return v_x_2330_;
}
else
{
lean_object* v_key_2332_; lean_object* v_value_2333_; lean_object* v_tail_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2357_; 
v_key_2332_ = lean_ctor_get(v_x_2331_, 0);
v_value_2333_ = lean_ctor_get(v_x_2331_, 1);
v_tail_2334_ = lean_ctor_get(v_x_2331_, 2);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_x_2331_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2336_ = v_x_2331_;
v_isShared_2337_ = v_isSharedCheck_2357_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_tail_2334_);
lean_inc(v_value_2333_);
lean_inc(v_key_2332_);
lean_dec(v_x_2331_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2357_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; uint64_t v___x_2339_; uint64_t v___x_2340_; uint64_t v___x_2341_; uint64_t v_fold_2342_; uint64_t v___x_2343_; uint64_t v___x_2344_; uint64_t v___x_2345_; size_t v___x_2346_; size_t v___x_2347_; size_t v___x_2348_; size_t v___x_2349_; size_t v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2338_ = lean_array_get_size(v_x_2330_);
v___x_2339_ = l_Lean_ExprStructEq_hash(v_key_2332_);
v___x_2340_ = 32ULL;
v___x_2341_ = lean_uint64_shift_right(v___x_2339_, v___x_2340_);
v_fold_2342_ = lean_uint64_xor(v___x_2339_, v___x_2341_);
v___x_2343_ = 16ULL;
v___x_2344_ = lean_uint64_shift_right(v_fold_2342_, v___x_2343_);
v___x_2345_ = lean_uint64_xor(v_fold_2342_, v___x_2344_);
v___x_2346_ = lean_uint64_to_usize(v___x_2345_);
v___x_2347_ = lean_usize_of_nat(v___x_2338_);
v___x_2348_ = ((size_t)1ULL);
v___x_2349_ = lean_usize_sub(v___x_2347_, v___x_2348_);
v___x_2350_ = lean_usize_land(v___x_2346_, v___x_2349_);
v___x_2351_ = lean_array_uget_borrowed(v_x_2330_, v___x_2350_);
lean_inc(v___x_2351_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 2, v___x_2351_);
v___x_2353_ = v___x_2336_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_key_2332_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v_value_2333_);
lean_ctor_set(v_reuseFailAlloc_2356_, 2, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_array_uset(v_x_2330_, v___x_2350_, v___x_2353_);
v_x_2330_ = v___x_2354_;
v_x_2331_ = v_tail_2334_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(lean_object* v_i_2358_, lean_object* v_source_2359_, lean_object* v_target_2360_){
_start:
{
lean_object* v___x_2361_; uint8_t v___x_2362_; 
v___x_2361_ = lean_array_get_size(v_source_2359_);
v___x_2362_ = lean_nat_dec_lt(v_i_2358_, v___x_2361_);
if (v___x_2362_ == 0)
{
lean_dec_ref(v_source_2359_);
lean_dec(v_i_2358_);
return v_target_2360_;
}
else
{
lean_object* v_es_2363_; lean_object* v___x_2364_; lean_object* v_source_2365_; lean_object* v_target_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_es_2363_ = lean_array_fget(v_source_2359_, v_i_2358_);
v___x_2364_ = lean_box(0);
v_source_2365_ = lean_array_fset(v_source_2359_, v_i_2358_, v___x_2364_);
v_target_2366_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_target_2360_, v_es_2363_);
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = lean_nat_add(v_i_2358_, v___x_2367_);
lean_dec(v_i_2358_);
v_i_2358_ = v___x_2368_;
v_source_2359_ = v_source_2365_;
v_target_2360_ = v_target_2366_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12___redArg(lean_object* v_data_2370_){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v_nbuckets_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2371_ = lean_array_get_size(v_data_2370_);
v___x_2372_ = lean_unsigned_to_nat(2u);
v_nbuckets_2373_ = lean_nat_mul(v___x_2371_, v___x_2372_);
v___x_2374_ = lean_unsigned_to_nat(0u);
v___x_2375_ = lean_box(0);
v___x_2376_ = lean_mk_array(v_nbuckets_2373_, v___x_2375_);
v___x_2377_ = lean_array_propagate_mark(v_data_2370_, v___x_2376_);
v___x_2378_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v___x_2374_, v_data_2370_, v___x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(lean_object* v_a_2379_, lean_object* v_b_2380_, lean_object* v_x_2381_){
_start:
{
if (lean_obj_tag(v_x_2381_) == 0)
{
lean_dec(v_b_2380_);
lean_dec_ref(v_a_2379_);
return v_x_2381_;
}
else
{
lean_object* v_key_2382_; lean_object* v_value_2383_; lean_object* v_tail_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2396_; 
v_key_2382_ = lean_ctor_get(v_x_2381_, 0);
v_value_2383_ = lean_ctor_get(v_x_2381_, 1);
v_tail_2384_ = lean_ctor_get(v_x_2381_, 2);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_x_2381_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2386_ = v_x_2381_;
v_isShared_2387_ = v_isSharedCheck_2396_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_tail_2384_);
lean_inc(v_value_2383_);
lean_inc(v_key_2382_);
lean_dec(v_x_2381_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2396_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
uint8_t v___x_2388_; 
v___x_2388_ = l_Lean_ExprStructEq_beq(v_key_2382_, v_a_2379_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2389_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(v_a_2379_, v_b_2380_, v_tail_2384_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 2, v___x_2389_);
v___x_2391_ = v___x_2386_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_key_2382_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_value_2383_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
else
{
lean_object* v___x_2394_; 
lean_dec(v_value_2383_);
lean_dec(v_key_2382_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 1, v_b_2380_);
lean_ctor_set(v___x_2386_, 0, v_a_2379_);
v___x_2394_ = v___x_2386_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2379_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_b_2380_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_tail_2384_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_a_2397_, lean_object* v_x_2398_){
_start:
{
if (lean_obj_tag(v_x_2398_) == 0)
{
uint8_t v___x_2399_; 
v___x_2399_ = 0;
return v___x_2399_;
}
else
{
lean_object* v_key_2400_; lean_object* v_tail_2401_; uint8_t v___x_2402_; 
v_key_2400_ = lean_ctor_get(v_x_2398_, 0);
v_tail_2401_ = lean_ctor_get(v_x_2398_, 2);
v___x_2402_ = l_Lean_ExprStructEq_beq(v_key_2400_, v_a_2397_);
if (v___x_2402_ == 0)
{
v_x_2398_ = v_tail_2401_;
goto _start;
}
else
{
return v___x_2402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object* v_a_2404_, lean_object* v_x_2405_){
_start:
{
uint8_t v_res_2406_; lean_object* v_r_2407_; 
v_res_2406_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_a_2404_, v_x_2405_);
lean_dec(v_x_2405_);
lean_dec_ref(v_a_2404_);
v_r_2407_ = lean_box(v_res_2406_);
return v_r_2407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(lean_object* v_m_2408_, lean_object* v_a_2409_, lean_object* v_b_2410_){
_start:
{
lean_object* v_size_2411_; lean_object* v_buckets_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2455_; 
v_size_2411_ = lean_ctor_get(v_m_2408_, 0);
v_buckets_2412_ = lean_ctor_get(v_m_2408_, 1);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_m_2408_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2414_ = v_m_2408_;
v_isShared_2415_ = v_isSharedCheck_2455_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_buckets_2412_);
lean_inc(v_size_2411_);
lean_dec(v_m_2408_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2455_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; uint64_t v___x_2417_; uint64_t v___x_2418_; uint64_t v___x_2419_; uint64_t v_fold_2420_; uint64_t v___x_2421_; uint64_t v___x_2422_; uint64_t v___x_2423_; size_t v___x_2424_; size_t v___x_2425_; size_t v___x_2426_; size_t v___x_2427_; size_t v___x_2428_; lean_object* v_bkt_2429_; uint8_t v___x_2430_; 
v___x_2416_ = lean_array_get_size(v_buckets_2412_);
v___x_2417_ = l_Lean_ExprStructEq_hash(v_a_2409_);
v___x_2418_ = 32ULL;
v___x_2419_ = lean_uint64_shift_right(v___x_2417_, v___x_2418_);
v_fold_2420_ = lean_uint64_xor(v___x_2417_, v___x_2419_);
v___x_2421_ = 16ULL;
v___x_2422_ = lean_uint64_shift_right(v_fold_2420_, v___x_2421_);
v___x_2423_ = lean_uint64_xor(v_fold_2420_, v___x_2422_);
v___x_2424_ = lean_uint64_to_usize(v___x_2423_);
v___x_2425_ = lean_usize_of_nat(v___x_2416_);
v___x_2426_ = ((size_t)1ULL);
v___x_2427_ = lean_usize_sub(v___x_2425_, v___x_2426_);
v___x_2428_ = lean_usize_land(v___x_2424_, v___x_2427_);
v_bkt_2429_ = lean_array_uget_borrowed(v_buckets_2412_, v___x_2428_);
v___x_2430_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_a_2409_, v_bkt_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v_size_x27_2432_; lean_object* v___x_2433_; lean_object* v_buckets_x27_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2431_ = lean_unsigned_to_nat(1u);
v_size_x27_2432_ = lean_nat_add(v_size_2411_, v___x_2431_);
lean_dec(v_size_2411_);
lean_inc(v_bkt_2429_);
v___x_2433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2433_, 0, v_a_2409_);
lean_ctor_set(v___x_2433_, 1, v_b_2410_);
lean_ctor_set(v___x_2433_, 2, v_bkt_2429_);
v_buckets_x27_2434_ = lean_array_uset(v_buckets_2412_, v___x_2428_, v___x_2433_);
v___x_2435_ = lean_unsigned_to_nat(4u);
v___x_2436_ = lean_nat_mul(v_size_x27_2432_, v___x_2435_);
v___x_2437_ = lean_unsigned_to_nat(3u);
v___x_2438_ = lean_nat_div(v___x_2436_, v___x_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_array_get_size(v_buckets_x27_2434_);
v___x_2440_ = lean_nat_dec_le(v___x_2438_, v___x_2439_);
lean_dec(v___x_2438_);
if (v___x_2440_ == 0)
{
lean_object* v_val_2441_; lean_object* v___x_2443_; 
v_val_2441_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12___redArg(v_buckets_x27_2434_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 1, v_val_2441_);
lean_ctor_set(v___x_2414_, 0, v_size_x27_2432_);
v___x_2443_ = v___x_2414_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_size_x27_2432_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_val_2441_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
else
{
lean_object* v___x_2446_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 1, v_buckets_x27_2434_);
lean_ctor_set(v___x_2414_, 0, v_size_x27_2432_);
v___x_2446_ = v___x_2414_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_size_x27_2432_);
lean_ctor_set(v_reuseFailAlloc_2447_, 1, v_buckets_x27_2434_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
else
{
lean_object* v___x_2448_; lean_object* v_buckets_x27_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
lean_inc(v_bkt_2429_);
v___x_2448_ = lean_box(0);
v_buckets_x27_2449_ = lean_array_uset(v_buckets_2412_, v___x_2428_, v___x_2448_);
v___x_2450_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(v_a_2409_, v_b_2410_, v_bkt_2429_);
v___x_2451_ = lean_array_uset(v_buckets_x27_2449_, v___x_2428_, v___x_2450_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 1, v___x_2451_);
v___x_2453_ = v___x_2414_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_size_2411_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2(lean_object* v_a_2456_, lean_object* v_e_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2460_ = lean_st_ref_take(v_a_2456_);
v___x_2461_ = lean_box(0);
v___x_2462_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v___x_2460_, v_e_2457_, v_a_2458_);
v___x_2463_ = lean_st_ref_put(v_a_2456_, v___x_2462_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2464_, lean_object* v_e_2465_, lean_object* v_a_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2(v_a_2464_, v_e_2465_, v_a_2466_);
lean_dec(v_a_2464_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2469_, lean_object* v_x_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_apply_1(v_x_2470_, lean_box(0));
v___x_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(v_00_u03b1_2476_, v_x_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_a_2482_, lean_object* v_x_2483_){
_start:
{
if (lean_obj_tag(v_x_2483_) == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_box(0);
return v___x_2484_;
}
else
{
lean_object* v_key_2485_; lean_object* v_value_2486_; lean_object* v_tail_2487_; uint8_t v___x_2488_; 
v_key_2485_ = lean_ctor_get(v_x_2483_, 0);
v_value_2486_ = lean_ctor_get(v_x_2483_, 1);
v_tail_2487_ = lean_ctor_get(v_x_2483_, 2);
v___x_2488_ = l_Lean_ExprStructEq_beq(v_key_2485_, v_a_2482_);
if (v___x_2488_ == 0)
{
v_x_2483_ = v_tail_2487_;
goto _start;
}
else
{
lean_object* v___x_2490_; 
lean_inc(v_value_2486_);
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_value_2486_);
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_a_2491_, lean_object* v_x_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2_spec__3___redArg(v_a_2491_, v_x_2492_);
lean_dec(v_x_2492_);
lean_dec_ref(v_a_2491_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___redArg(lean_object* v_m_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_buckets_2496_; lean_object* v___x_2497_; uint64_t v___x_2498_; uint64_t v___x_2499_; uint64_t v___x_2500_; uint64_t v_fold_2501_; uint64_t v___x_2502_; uint64_t v___x_2503_; uint64_t v___x_2504_; size_t v___x_2505_; size_t v___x_2506_; size_t v___x_2507_; size_t v___x_2508_; size_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_buckets_2496_ = lean_ctor_get(v_m_2494_, 1);
v___x_2497_ = lean_array_get_size(v_buckets_2496_);
v___x_2498_ = l_Lean_ExprStructEq_hash(v_a_2495_);
v___x_2499_ = 32ULL;
v___x_2500_ = lean_uint64_shift_right(v___x_2498_, v___x_2499_);
v_fold_2501_ = lean_uint64_xor(v___x_2498_, v___x_2500_);
v___x_2502_ = 16ULL;
v___x_2503_ = lean_uint64_shift_right(v_fold_2501_, v___x_2502_);
v___x_2504_ = lean_uint64_xor(v_fold_2501_, v___x_2503_);
v___x_2505_ = lean_uint64_to_usize(v___x_2504_);
v___x_2506_ = lean_usize_of_nat(v___x_2497_);
v___x_2507_ = ((size_t)1ULL);
v___x_2508_ = lean_usize_sub(v___x_2506_, v___x_2507_);
v___x_2509_ = lean_usize_land(v___x_2505_, v___x_2508_);
v___x_2510_ = lean_array_uget_borrowed(v_buckets_2496_, v___x_2509_);
v___x_2511_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2_spec__3___redArg(v_a_2495_, v___x_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___redArg(v_m_2512_, v_a_2513_);
lean_dec_ref(v_a_2513_);
lean_dec_ref(v_m_2512_);
return v_res_2514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2516_; lean_object* v_dummy_2517_; 
v___x_2516_ = lean_box(0);
v_dummy_2517_ = l_Lean_Expr_sort___override(v___x_2516_);
return v_dummy_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(lean_object* v_pre_2518_, lean_object* v_post_2519_, size_t v_sz_2520_, size_t v_i_2521_, lean_object* v_bs_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
uint8_t v___x_2527_; 
v___x_2527_ = lean_usize_dec_lt(v_i_2521_, v_sz_2520_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; 
lean_dec_ref(v_post_2519_);
lean_dec_ref(v_pre_2518_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v_bs_2522_);
return v___x_2528_;
}
else
{
lean_object* v_v_2529_; lean_object* v___x_2530_; lean_object* v_bs_x27_2531_; lean_object* v___x_2532_; 
v_v_2529_ = lean_array_uget(v_bs_2522_, v_i_2521_);
v___x_2530_ = lean_unsigned_to_nat(0u);
v_bs_x27_2531_ = lean_array_uset(v_bs_2522_, v_i_2521_, v___x_2530_);
lean_inc_ref(v_post_2519_);
lean_inc_ref(v_pre_2518_);
v___x_2532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2518_, v_post_2519_, v_v_2529_, v___y_2523_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; size_t v___x_2534_; size_t v___x_2535_; lean_object* v___x_2536_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v___x_2534_ = ((size_t)1ULL);
v___x_2535_ = lean_usize_add(v_i_2521_, v___x_2534_);
v___x_2536_ = lean_array_uset(v_bs_x27_2531_, v_i_2521_, v_a_2533_);
v_i_2521_ = v___x_2535_;
v_bs_2522_ = v___x_2536_;
goto _start;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec_ref(v_bs_x27_2531_);
lean_dec_ref(v_post_2519_);
lean_dec_ref(v_pre_2518_);
v_a_2538_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2532_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2532_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(lean_object* v_pre_2546_, lean_object* v_post_2547_, lean_object* v___y_2548_, lean_object* v_x_2549_, lean_object* v_x_2550_, lean_object* v_x_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
if (lean_obj_tag(v_x_2549_) == 5)
{
lean_object* v_fn_2556_; lean_object* v_arg_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v_fn_2556_ = lean_ctor_get(v_x_2549_, 0);
lean_inc_ref(v_fn_2556_);
v_arg_2557_ = lean_ctor_get(v_x_2549_, 1);
lean_inc_ref(v_arg_2557_);
lean_dec_ref_known(v_x_2549_, 2);
v___x_2558_ = lean_array_set(v_x_2550_, v_x_2551_, v_arg_2557_);
v___x_2559_ = lean_unsigned_to_nat(1u);
v___x_2560_ = lean_nat_sub(v_x_2551_, v___x_2559_);
lean_dec(v_x_2551_);
v_x_2549_ = v_fn_2556_;
v_x_2550_ = v___x_2558_;
v_x_2551_ = v___x_2560_;
goto _start;
}
else
{
lean_object* v___x_2562_; 
lean_dec(v_x_2551_);
lean_inc_ref(v_post_2547_);
lean_inc_ref(v_pre_2546_);
v___x_2562_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2546_, v_post_2547_, v_x_2549_, v___y_2552_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; size_t v_sz_2564_; size_t v___x_2565_; lean_object* v___x_2566_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v_sz_2564_ = lean_array_size(v_x_2550_);
v___x_2565_ = ((size_t)0ULL);
v___x_2566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2546_, v_post_2547_, v_sz_2564_, v___x_2565_, v_x_2550_, v___y_2552_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2575_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2571_ = l_Lean_Expr_updateAppN(v___y_2548_, v_a_2563_, v_a_2567_);
lean_dec(v_a_2567_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2571_);
v___x_2573_ = v___x_2569_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v_a_2563_);
v_a_2576_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2566_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2566_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_dec_ref(v_x_2550_);
lean_dec_ref(v_post_2547_);
lean_dec_ref(v_pre_2546_);
return v___x_2562_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object* v___x_2584_, lean_object* v_pre_2585_, lean_object* v_e_2586_, lean_object* v_post_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_Core_checkSystem(v___x_2584_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v___x_2593_; 
lean_dec_ref_known(v___x_2592_, 1);
lean_inc_ref(v_pre_2585_);
lean_inc(v___y_2590_);
lean_inc_ref(v___y_2589_);
lean_inc_ref(v_e_2586_);
v___x_2593_ = lean_apply_4(v_pre_2585_, v_e_2586_, v___y_2589_, v___y_2590_, lean_box(0));
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2711_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2711_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2711_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___y_2599_; 
switch(lean_obj_tag(v_a_2594_))
{
case 0:
{
lean_object* v_e_2701_; lean_object* v___x_2703_; 
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_e_2586_);
lean_dec_ref(v_pre_2585_);
v_e_2701_ = lean_ctor_get(v_a_2594_, 0);
lean_inc_ref(v_e_2701_);
lean_dec_ref_known(v_a_2594_, 1);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v_e_2701_);
v___x_2703_ = v___x_2596_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_e_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
case 1:
{
lean_object* v_e_2705_; lean_object* v___x_2706_; 
lean_del_object(v___x_2596_);
lean_dec_ref(v_e_2586_);
v_e_2705_ = lean_ctor_get(v_a_2594_, 0);
lean_inc_ref(v_e_2705_);
lean_dec_ref_known(v_a_2594_, 1);
lean_inc_ref(v_post_2587_);
lean_inc_ref(v_pre_2585_);
v___x_2706_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2585_, v_post_2587_, v_e_2705_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2708_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2706_, 1);
v___x_2708_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v_a_2707_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2708_;
}
else
{
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_pre_2585_);
return v___x_2706_;
}
}
default: 
{
lean_object* v_e_x3f_2709_; 
lean_del_object(v___x_2596_);
v_e_x3f_2709_ = lean_ctor_get(v_a_2594_, 0);
lean_inc(v_e_x3f_2709_);
lean_dec_ref_known(v_a_2594_, 1);
if (lean_obj_tag(v_e_x3f_2709_) == 0)
{
v___y_2599_ = v_e_2586_;
goto v___jp_2598_;
}
else
{
lean_object* v_val_2710_; 
lean_dec_ref(v_e_2586_);
v_val_2710_ = lean_ctor_get(v_e_x3f_2709_, 0);
lean_inc(v_val_2710_);
lean_dec_ref_known(v_e_x3f_2709_, 1);
v___y_2599_ = v_val_2710_;
goto v___jp_2598_;
}
}
}
v___jp_2598_:
{
switch(lean_obj_tag(v___y_2599_))
{
case 7:
{
lean_object* v_binderName_2600_; lean_object* v_binderType_2601_; lean_object* v_body_2602_; uint8_t v_binderInfo_2603_; lean_object* v___x_2604_; 
v_binderName_2600_ = lean_ctor_get(v___y_2599_, 0);
v_binderType_2601_ = lean_ctor_get(v___y_2599_, 1);
v_body_2602_ = lean_ctor_get(v___y_2599_, 2);
v_binderInfo_2603_ = lean_ctor_get_uint8(v___y_2599_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2601_);
lean_inc_ref(v_post_2587_);
lean_inc_ref(v_pre_2585_);
v___x_2604_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2585_, v_post_2587_, v_binderType_2601_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
lean_inc_ref(v_body_2602_);
lean_inc_ref(v_post_2587_);
lean_inc_ref(v_pre_2585_);
v___x_2606_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2585_, v_post_2587_, v_body_2602_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; size_t v___x_2608_; size_t v___x_2609_; uint8_t v___x_2610_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v___x_2608_ = lean_ptr_addr(v_binderType_2601_);
v___x_2609_ = lean_ptr_addr(v_a_2605_);
v___x_2610_ = lean_usize_dec_eq(v___x_2608_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
lean_inc(v_binderName_2600_);
lean_dec_ref_known(v___y_2599_, 3);
v___x_2611_ = l_Lean_Expr_forallE___override(v_binderName_2600_, v_a_2605_, v_a_2607_, v_binderInfo_2603_);
v___x_2612_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___x_2611_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2612_;
}
else
{
size_t v___x_2613_; size_t v___x_2614_; uint8_t v___x_2615_; 
v___x_2613_ = lean_ptr_addr(v_body_2602_);
v___x_2614_ = lean_ptr_addr(v_a_2607_);
v___x_2615_ = lean_usize_dec_eq(v___x_2613_, v___x_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_inc(v_binderName_2600_);
lean_dec_ref_known(v___y_2599_, 3);
v___x_2616_ = l_Lean_Expr_forallE___override(v_binderName_2600_, v_a_2605_, v_a_2607_, v_binderInfo_2603_);
v___x_2617_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___x_2616_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2617_;
}
else
{
uint8_t v___x_2618_; 
v___x_2618_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2603_, v_binderInfo_2603_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_inc(v_binderName_2600_);
lean_dec_ref_known(v___y_2599_, 3);
v___x_2619_ = l_Lean_Expr_forallE___override(v_binderName_2600_, v_a_2605_, v_a_2607_, v_binderInfo_2603_);
v___x_2620_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___x_2619_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2620_;
}
else
{
lean_object* v___x_2621_; 
lean_dec(v_a_2607_);
lean_dec(v_a_2605_);
v___x_2621_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___y_2599_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2621_;
}
}
}
}
else
{
lean_dec(v_a_2605_);
lean_dec_ref_known(v___y_2599_, 3);
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_pre_2585_);
return v___x_2606_;
}
}
else
{
lean_dec_ref_known(v___y_2599_, 3);
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_pre_2585_);
return v___x_2604_;
}
}
case 6:
{
lean_object* v_binderName_2622_; lean_object* v_binderType_2623_; lean_object* v_body_2624_; uint8_t v_binderInfo_2625_; lean_object* v___x_2626_; 
v_binderName_2622_ = lean_ctor_get(v___y_2599_, 0);
v_binderType_2623_ = lean_ctor_get(v___y_2599_, 1);
v_body_2624_ = lean_ctor_get(v___y_2599_, 2);
v_binderInfo_2625_ = lean_ctor_get_uint8(v___y_2599_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2623_);
lean_inc_ref(v_post_2587_);
lean_inc_ref(v_pre_2585_);
v___x_2626_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2585_, v_post_2587_, v_binderType_2623_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2628_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2626_, 1);
lean_inc_ref(v_body_2624_);
lean_inc_ref(v_post_2587_);
lean_inc_ref(v_pre_2585_);
v___x_2628_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2585_, v_post_2587_, v_body_2624_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; size_t v___x_2630_; size_t v___x_2631_; uint8_t v___x_2632_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2628_, 1);
v___x_2630_ = lean_ptr_addr(v_binderType_2623_);
v___x_2631_ = lean_ptr_addr(v_a_2627_);
v___x_2632_ = lean_usize_dec_eq(v___x_2630_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_inc(v_binderName_2622_);
lean_dec_ref_known(v___y_2599_, 3);
v___x_2633_ = l_Lean_Expr_lam___override(v_binderName_2622_, v_a_2627_, v_a_2629_, v_binderInfo_2625_);
v___x_2634_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___x_2633_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2634_;
}
else
{
size_t v___x_2635_; size_t v___x_2636_; uint8_t v___x_2637_; 
v___x_2635_ = lean_ptr_addr(v_body_2624_);
v___x_2636_ = lean_ptr_addr(v_a_2629_);
v___x_2637_ = lean_usize_dec_eq(v___x_2635_, v___x_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_inc(v_binderName_2622_);
lean_dec_ref_known(v___y_2599_, 3);
v___x_2638_ = l_Lean_Expr_lam___override(v_binderName_2622_, v_a_2627_, v_a_2629_, v_binderInfo_2625_);
v___x_2639_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___x_2638_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2639_;
}
else
{
uint8_t v___x_2640_; 
v___x_2640_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2625_, v_binderInfo_2625_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_inc(v_binderName_2622_);
lean_dec_ref_known(v___y_2599_, 3);
v___x_2641_ = l_Lean_Expr_lam___override(v_binderName_2622_, v_a_2627_, v_a_2629_, v_binderInfo_2625_);
v___x_2642_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___x_2641_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2642_;
}
else
{
lean_object* v___x_2643_; 
lean_dec(v_a_2629_);
lean_dec(v_a_2627_);
v___x_2643_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___y_2599_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2643_;
}
}
}
}
else
{
lean_dec(v_a_2627_);
lean_dec_ref_known(v___y_2599_, 3);
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_pre_2585_);
return v___x_2628_;
}
}
else
{
lean_dec_ref_known(v___y_2599_, 3);
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_pre_2585_);
return v___x_2626_;
}
}
case 8:
{
lean_object* v_declName_2644_; lean_object* v_type_2645_; lean_object* v_value_2646_; lean_object* v_body_2647_; uint8_t v_nondep_2648_; lean_object* v___x_2649_; 
v_declName_2644_ = lean_ctor_get(v___y_2599_, 0);
v_type_2645_ = lean_ctor_get(v___y_2599_, 1);
v_value_2646_ = lean_ctor_get(v___y_2599_, 2);
v_body_2647_ = lean_ctor_get(v___y_2599_, 3);
v_nondep_2648_ = lean_ctor_get_uint8(v___y_2599_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2645_);
lean_inc_ref(v_post_2587_);
lean_inc_ref(v_pre_2585_);
v___x_2649_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2585_, v_post_2587_, v_type_2645_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2651_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
lean_inc_ref(v_value_2646_);
lean_inc_ref(v_post_2587_);
lean_inc_ref(v_pre_2585_);
v___x_2651_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2585_, v_post_2587_, v_value_2646_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2653_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
lean_inc_ref(v_body_2647_);
lean_inc_ref(v_post_2587_);
lean_inc_ref(v_pre_2585_);
v___x_2653_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2585_, v_post_2587_, v_body_2647_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; size_t v___x_2655_; size_t v___x_2656_; uint8_t v___x_2657_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v___x_2655_ = lean_ptr_addr(v_type_2645_);
v___x_2656_ = lean_ptr_addr(v_a_2650_);
v___x_2657_ = lean_usize_dec_eq(v___x_2655_, v___x_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_inc(v_declName_2644_);
lean_dec_ref_known(v___y_2599_, 4);
v___x_2658_ = l_Lean_Expr_letE___override(v_declName_2644_, v_a_2650_, v_a_2652_, v_a_2654_, v_nondep_2648_);
v___x_2659_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___x_2658_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2659_;
}
else
{
size_t v___x_2660_; size_t v___x_2661_; uint8_t v___x_2662_; 
v___x_2660_ = lean_ptr_addr(v_value_2646_);
v___x_2661_ = lean_ptr_addr(v_a_2652_);
v___x_2662_ = lean_usize_dec_eq(v___x_2660_, v___x_2661_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
lean_inc(v_declName_2644_);
lean_dec_ref_known(v___y_2599_, 4);
v___x_2663_ = l_Lean_Expr_letE___override(v_declName_2644_, v_a_2650_, v_a_2652_, v_a_2654_, v_nondep_2648_);
v___x_2664_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___x_2663_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2664_;
}
else
{
size_t v___x_2665_; size_t v___x_2666_; uint8_t v___x_2667_; 
v___x_2665_ = lean_ptr_addr(v_body_2647_);
v___x_2666_ = lean_ptr_addr(v_a_2654_);
v___x_2667_ = lean_usize_dec_eq(v___x_2665_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_inc(v_declName_2644_);
lean_dec_ref_known(v___y_2599_, 4);
v___x_2668_ = l_Lean_Expr_letE___override(v_declName_2644_, v_a_2650_, v_a_2652_, v_a_2654_, v_nondep_2648_);
v___x_2669_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___x_2668_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2669_;
}
else
{
lean_object* v___x_2670_; 
lean_dec(v_a_2654_);
lean_dec(v_a_2652_);
lean_dec(v_a_2650_);
v___x_2670_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___y_2599_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2670_;
}
}
}
}
else
{
lean_dec(v_a_2652_);
lean_dec(v_a_2650_);
lean_dec_ref_known(v___y_2599_, 4);
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_pre_2585_);
return v___x_2653_;
}
}
else
{
lean_dec(v_a_2650_);
lean_dec_ref_known(v___y_2599_, 4);
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_pre_2585_);
return v___x_2651_;
}
}
else
{
lean_dec_ref_known(v___y_2599_, 4);
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_pre_2585_);
return v___x_2649_;
}
}
case 5:
{
lean_object* v_dummy_2671_; lean_object* v_nargs_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_dummy_2671_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0);
v_nargs_2672_ = l_Lean_Expr_getAppNumArgs(v___y_2599_);
lean_inc(v_nargs_2672_);
v___x_2673_ = lean_mk_array(v_nargs_2672_, v_dummy_2671_);
v___x_2674_ = lean_unsigned_to_nat(1u);
v___x_2675_ = lean_nat_sub(v_nargs_2672_, v___x_2674_);
lean_dec(v_nargs_2672_);
lean_inc_ref(v___y_2599_);
lean_inc_ref(v_post_2587_);
lean_inc_ref(v_pre_2585_);
v___x_2676_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_pre_2585_, v_post_2587_, v___y_2599_, v___y_2599_, v___x_2673_, v___x_2675_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec_ref_known(v___y_2599_, 2);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v___x_2678_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v_a_2677_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2678_;
}
else
{
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_pre_2585_);
return v___x_2676_;
}
}
case 10:
{
lean_object* v_data_2679_; lean_object* v_expr_2680_; lean_object* v___x_2681_; 
v_data_2679_ = lean_ctor_get(v___y_2599_, 0);
v_expr_2680_ = lean_ctor_get(v___y_2599_, 1);
lean_inc_ref(v_expr_2680_);
lean_inc_ref(v_post_2587_);
lean_inc_ref(v_pre_2585_);
v___x_2681_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2585_, v_post_2587_, v_expr_2680_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; size_t v___x_2683_; size_t v___x_2684_; uint8_t v___x_2685_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2681_, 1);
v___x_2683_ = lean_ptr_addr(v_expr_2680_);
v___x_2684_ = lean_ptr_addr(v_a_2682_);
v___x_2685_ = lean_usize_dec_eq(v___x_2683_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_inc(v_data_2679_);
lean_dec_ref_known(v___y_2599_, 2);
v___x_2686_ = l_Lean_Expr_mdata___override(v_data_2679_, v_a_2682_);
v___x_2687_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___x_2686_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2687_;
}
else
{
lean_object* v___x_2688_; 
lean_dec(v_a_2682_);
v___x_2688_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___y_2599_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2688_;
}
}
else
{
lean_dec_ref_known(v___y_2599_, 2);
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_pre_2585_);
return v___x_2681_;
}
}
case 11:
{
lean_object* v_typeName_2689_; lean_object* v_idx_2690_; lean_object* v_struct_2691_; lean_object* v___x_2692_; 
v_typeName_2689_ = lean_ctor_get(v___y_2599_, 0);
v_idx_2690_ = lean_ctor_get(v___y_2599_, 1);
v_struct_2691_ = lean_ctor_get(v___y_2599_, 2);
lean_inc_ref(v_struct_2691_);
lean_inc_ref(v_post_2587_);
lean_inc_ref(v_pre_2585_);
v___x_2692_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2585_, v_post_2587_, v_struct_2691_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; size_t v___x_2694_; size_t v___x_2695_; uint8_t v___x_2696_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2692_, 1);
v___x_2694_ = lean_ptr_addr(v_struct_2691_);
v___x_2695_ = lean_ptr_addr(v_a_2693_);
v___x_2696_ = lean_usize_dec_eq(v___x_2694_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_inc(v_idx_2690_);
lean_inc(v_typeName_2689_);
lean_dec_ref_known(v___y_2599_, 3);
v___x_2697_ = l_Lean_Expr_proj___override(v_typeName_2689_, v_idx_2690_, v_a_2693_);
v___x_2698_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___x_2697_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2698_;
}
else
{
lean_object* v___x_2699_; 
lean_dec(v_a_2693_);
v___x_2699_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___y_2599_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2699_;
}
}
else
{
lean_dec_ref_known(v___y_2599_, 3);
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_pre_2585_);
return v___x_2692_;
}
}
default: 
{
lean_object* v___x_2700_; 
v___x_2700_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2585_, v_post_2587_, v___y_2599_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2700_;
}
}
}
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_e_2586_);
lean_dec_ref(v_pre_2585_);
v_a_2712_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2593_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2593_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec_ref(v_post_2587_);
lean_dec_ref(v_e_2586_);
lean_dec_ref(v_pre_2585_);
v_a_2720_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2592_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2592_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object* v___x_2728_, lean_object* v_pre_2729_, lean_object* v_e_2730_, lean_object* v_post_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(v___x_2728_, v_pre_2729_, v_e_2730_, v_post_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(lean_object* v_pre_2737_, lean_object* v_post_2738_, lean_object* v_e_2739_, lean_object* v_a_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_inc(v_a_2740_);
v___x_2744_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2744_, 0, lean_box(0));
lean_closure_set(v___x_2744_, 1, lean_box(0));
lean_closure_set(v___x_2744_, 2, v_a_2740_);
v___x_2745_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___x_2744_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2777_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2748_ = v___x_2745_;
v_isShared_2749_ = v_isSharedCheck_2777_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2777_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___redArg(v_a_2746_, v_e_2739_);
lean_dec(v_a_2746_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v___x_2751_; lean_object* v___f_2752_; lean_object* v___x_2753_; 
lean_del_object(v___x_2748_);
v___x_2751_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___closed__0));
lean_inc_ref(v_e_2739_);
v___f_2752_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed), 8, 4);
lean_closure_set(v___f_2752_, 0, v___x_2751_);
lean_closure_set(v___f_2752_, 1, v_pre_2737_);
lean_closure_set(v___f_2752_, 2, v_e_2739_);
lean_closure_set(v___f_2752_, 3, v_post_2738_);
v___x_2753_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v___f_2752_, v_a_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___f_2755_; lean_object* v___x_2756_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc_n(v_a_2754_, 2);
lean_dec_ref_known(v___x_2753_, 1);
lean_inc(v_a_2740_);
v___f_2755_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2755_, 0, v_a_2740_);
lean_closure_set(v___f_2755_, 1, v_e_2739_);
lean_closure_set(v___f_2755_, 2, v_a_2754_);
v___x_2756_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___f_2755_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2763_ == 0)
{
lean_object* v_unused_2764_; 
v_unused_2764_ = lean_ctor_get(v___x_2756_, 0);
lean_dec(v_unused_2764_);
v___x_2758_ = v___x_2756_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_dec(v___x_2756_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v_a_2754_);
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2754_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec(v_a_2754_);
v_a_2765_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2756_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2756_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
else
{
lean_dec_ref(v_e_2739_);
return v___x_2753_;
}
}
else
{
lean_object* v_val_2773_; lean_object* v___x_2775_; 
lean_dec_ref(v_e_2739_);
lean_dec_ref(v_post_2738_);
lean_dec_ref(v_pre_2737_);
v_val_2773_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_val_2773_);
lean_dec_ref_known(v___x_2750_, 1);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v_val_2773_);
v___x_2775_ = v___x_2748_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_val_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec_ref(v_e_2739_);
lean_dec_ref(v_post_2738_);
lean_dec_ref(v_pre_2737_);
v_a_2778_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2745_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2745_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object* v_pre_2786_, lean_object* v_post_2787_, lean_object* v_e_2788_, lean_object* v_a_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; 
lean_inc_ref(v_post_2787_);
lean_inc(v___y_2791_);
lean_inc_ref(v___y_2790_);
lean_inc_ref(v_e_2788_);
v___x_2793_ = lean_apply_4(v_post_2787_, v_e_2788_, v___y_2790_, v___y_2791_, lean_box(0));
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2812_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2812_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2812_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
switch(lean_obj_tag(v_a_2794_))
{
case 0:
{
lean_object* v_e_2798_; lean_object* v___x_2800_; 
lean_dec_ref(v_e_2788_);
lean_dec_ref(v_post_2787_);
lean_dec_ref(v_pre_2786_);
v_e_2798_ = lean_ctor_get(v_a_2794_, 0);
lean_inc_ref(v_e_2798_);
lean_dec_ref_known(v_a_2794_, 1);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v_e_2798_);
v___x_2800_ = v___x_2796_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_e_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
case 1:
{
lean_object* v_e_2802_; lean_object* v___x_2803_; 
lean_del_object(v___x_2796_);
lean_dec_ref(v_e_2788_);
v_e_2802_ = lean_ctor_get(v_a_2794_, 0);
lean_inc_ref(v_e_2802_);
lean_dec_ref_known(v_a_2794_, 1);
v___x_2803_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2786_, v_post_2787_, v_e_2802_, v_a_2789_, v___y_2790_, v___y_2791_);
return v___x_2803_;
}
default: 
{
lean_object* v_e_x3f_2804_; 
lean_dec_ref(v_post_2787_);
lean_dec_ref(v_pre_2786_);
v_e_x3f_2804_ = lean_ctor_get(v_a_2794_, 0);
lean_inc(v_e_x3f_2804_);
lean_dec_ref_known(v_a_2794_, 1);
if (lean_obj_tag(v_e_x3f_2804_) == 0)
{
lean_object* v___x_2806_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v_e_2788_);
v___x_2806_ = v___x_2796_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_e_2788_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
else
{
lean_object* v_val_2808_; lean_object* v___x_2810_; 
lean_dec_ref(v_e_2788_);
v_val_2808_ = lean_ctor_get(v_e_x3f_2804_, 0);
lean_inc(v_val_2808_);
lean_dec_ref_known(v_e_x3f_2804_, 1);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v_val_2808_);
v___x_2810_ = v___x_2796_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_val_2808_);
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
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec_ref(v_e_2788_);
lean_dec_ref(v_post_2787_);
lean_dec_ref(v_pre_2786_);
v_a_2813_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2793_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2793_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(lean_object* v_pre_2821_, lean_object* v_post_2822_, lean_object* v_e_2823_, lean_object* v_a_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_2821_, v_post_2822_, v_e_2823_, v_a_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v_a_2824_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_2829_, lean_object* v_post_2830_, lean_object* v_sz_2831_, lean_object* v_i_2832_, lean_object* v_bs_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
size_t v_sz_boxed_2838_; size_t v_i_boxed_2839_; lean_object* v_res_2840_; 
v_sz_boxed_2838_ = lean_unbox_usize(v_sz_2831_);
lean_dec(v_sz_2831_);
v_i_boxed_2839_ = lean_unbox_usize(v_i_2832_);
lean_dec(v_i_2832_);
v_res_2840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2829_, v_post_2830_, v_sz_boxed_2838_, v_i_boxed_2839_, v_bs_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_2841_, lean_object* v_post_2842_, lean_object* v___y_2843_, lean_object* v_x_2844_, lean_object* v_x_2845_, lean_object* v_x_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_pre_2841_, v_post_2842_, v___y_2843_, v_x_2844_, v_x_2845_, v_x_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2843_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___boxed(lean_object* v_pre_2852_, lean_object* v_post_2853_, lean_object* v_e_2854_, lean_object* v_a_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2852_, v_post_2853_, v_e_2854_, v_a_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v_a_2855_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_object* v_00_u03b1_2860_, lean_object* v_x_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = lean_apply_1(v_x_2861_, lean_box(0));
v___x_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2867_, lean_object* v_x_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(v_00_u03b1_2867_, v_x_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2872_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__1, &l_Lean_Expr_checkMaxShared___closed__1_once, _init_l_Lean_Expr_checkMaxShared___closed__1);
v___x_2874_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2874_, 0, lean_box(0));
lean_closure_set(v___x_2874_, 1, lean_box(0));
lean_closure_set(v___x_2874_, 2, v___x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(lean_object* v_input_2875_, lean_object* v_pre_2876_, lean_object* v_post_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v_a_2883_; lean_object* v___x_2884_; 
v___x_2881_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0);
v___x_2882_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_2881_, v___y_2878_, v___y_2879_);
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2882_);
v___x_2884_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2876_, v_post_2877_, v_input_2875_, v_a_2883_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2884_, 1);
v___x_2886_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2886_, 0, lean_box(0));
lean_closure_set(v___x_2886_, 1, lean_box(0));
lean_closure_set(v___x_2886_, 2, v_a_2883_);
v___x_2887_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_2886_, v___y_2878_, v___y_2879_);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2894_ == 0)
{
lean_object* v_unused_2895_; 
v_unused_2895_ = lean_ctor_get(v___x_2887_, 0);
lean_dec(v_unused_2895_);
v___x_2889_ = v___x_2887_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_dec(v___x_2887_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 0, v_a_2885_);
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2885_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
else
{
lean_dec(v_a_2883_);
return v___x_2884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___boxed(lean_object* v_input_2896_, lean_object* v_pre_2897_, lean_object* v_post_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_input_2896_, v_pre_2897_, v_post_2898_, v___y_2899_, v___y_2900_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object* v_e_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
uint8_t v___x_2909_; 
v___x_2909_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_2905_);
if (v___x_2909_ == 0)
{
lean_object* v_pre_2910_; lean_object* v___f_2911_; lean_object* v___x_2912_; 
v_pre_2910_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__0));
v___f_2911_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__1));
v___x_2912_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_e_2905_, v_pre_2910_, v___f_2911_, v_a_2906_, v_a_2907_);
return v___x_2912_;
}
else
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v_e_2905_);
return v___x_2913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___boxed(lean_object* v_e_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_Meta_Sym_normalizeLevels(v_e_2914_, v_a_2915_, v_a_2916_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2919_, lean_object* v_m_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___redArg(v_m_2920_, v_a_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2923_, lean_object* v_m_2924_, lean_object* v_a_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_00_u03b2_2923_, v_m_2924_, v_a_2925_);
lean_dec_ref(v_a_2925_);
lean_dec_ref(v_m_2924_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_2927_, lean_object* v_ref_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2928_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2933_, lean_object* v_ref_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_2933_, v_ref_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9(v_00_u03b1_2944_, v___y_2945_, v___y_2946_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6(lean_object* v_00_u03b1_2949_, lean_object* v_x_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v_x_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b1_2956_, lean_object* v_x_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6(v_00_u03b1_2956_, v_x_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_2963_, lean_object* v_m_2964_, lean_object* v_a_2965_, lean_object* v_b_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v_m_2964_, v_a_2965_, v_b_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2968_, lean_object* v_a_2969_, lean_object* v_x_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2_spec__3___redArg(v_a_2969_, v_x_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2972_, lean_object* v_a_2973_, lean_object* v_x_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2_spec__3(v_00_u03b2_2972_, v_a_2973_, v_x_2974_);
lean_dec(v_x_2974_);
lean_dec_ref(v_a_2973_);
return v_res_2975_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_2976_, lean_object* v_a_2977_, lean_object* v_x_2978_){
_start:
{
uint8_t v___x_2979_; 
v___x_2979_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_a_2977_, v_x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_2980_, lean_object* v_a_2981_, lean_object* v_x_2982_){
_start:
{
uint8_t v_res_2983_; lean_object* v_r_2984_; 
v_res_2983_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_2980_, v_a_2981_, v_x_2982_);
lean_dec(v_x_2982_);
lean_dec_ref(v_a_2981_);
v_r_2984_ = lean_box(v_res_2983_);
return v_r_2984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_2985_, lean_object* v_data_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12___redArg(v_data_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13(lean_object* v_00_u03b2_2988_, lean_object* v_a_2989_, lean_object* v_b_2990_, lean_object* v_x_2991_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(v_a_2989_, v_b_2990_, v_x_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13(lean_object* v_00_u03b2_2993_, lean_object* v_i_2994_, lean_object* v_source_2995_, lean_object* v_target_2996_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v_i_2994_, v_source_2995_, v_target_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14(lean_object* v_00_u03b2_2998_, lean_object* v_x_2999_, lean_object* v_x_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_x_2999_, v_x_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0___redArg(lean_object* v_declName_3002_, lean_object* v_us_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = l_Lean_Expr_const___override(v_declName_3002_, v_us_3003_);
v___x_3007_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3006_, v___y_3004_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0___redArg___boxed(lean_object* v_declName_3008_, lean_object* v_us_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0___redArg(v_declName_3008_, v_us_3009_, v___y_3010_);
lean_dec(v___y_3010_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0(lean_object* v_declName_3013_, lean_object* v_us_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0___redArg(v_declName_3013_, v_us_3014_, v___y_3016_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0___boxed(lean_object* v_declName_3023_, lean_object* v_us_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0(v_declName_3023_, v_us_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_mkNotS_spec__1(lean_object* v_f_3033_, lean_object* v_a_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v___y_3043_; lean_object* v___x_3046_; uint8_t v_debug_3047_; 
v___x_3046_ = lean_st_ref_get(v___y_3036_);
v_debug_3047_ = lean_ctor_get_uint8(v___x_3046_, sizeof(void*)*13);
lean_dec(v___x_3046_);
if (v_debug_3047_ == 0)
{
v___y_3043_ = v___y_3036_;
goto v___jp_3042_;
}
else
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_3033_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v___x_3049_; 
lean_dec_ref_known(v___x_3048_, 1);
v___x_3049_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_dec_ref_known(v___x_3049_, 1);
v___y_3043_ = v___y_3036_;
goto v___jp_3042_;
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec_ref(v_a_3034_);
lean_dec_ref(v_f_3033_);
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3049_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3049_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec_ref(v_a_3034_);
lean_dec_ref(v_f_3033_);
v_a_3058_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3048_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3048_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
v___jp_3042_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = l_Lean_Expr_app___override(v_f_3033_, v_a_3034_);
v___x_3045_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3044_, v___y_3043_);
return v___x_3045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_mkNotS_spec__1___boxed(lean_object* v_f_3066_, lean_object* v_a_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_mkNotS_spec__1(v_f_3066_, v_a_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkNotS(lean_object* v_p_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3087_ = ((lean_object*)(l_Lean_Meta_Sym_mkNotS___closed__1));
v___x_3088_ = lean_box(0);
v___x_3089_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0___redArg(v___x_3087_, v___x_3088_, v_a_3081_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3091_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3090_);
lean_dec_ref_known(v___x_3089_, 1);
v___x_3091_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_mkNotS_spec__1(v_a_3090_, v_p_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
return v___x_3091_;
}
else
{
lean_dec_ref(v_p_3079_);
return v___x_3089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkNotS___boxed(lean_object* v_p_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_Lean_Meta_Sym_mkNotS(v_p_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
lean_dec(v_a_3098_);
lean_dec_ref(v_a_3097_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_mkAndS_spec__0(lean_object* v_f_3101_, lean_object* v_a_u2081_3102_, lean_object* v_a_u2082_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_mkNotS_spec__1(v_f_3101_, v_a_u2081_3102_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3113_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3112_);
lean_dec_ref_known(v___x_3111_, 1);
v___x_3113_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_mkNotS_spec__1(v_a_3112_, v_a_u2082_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
return v___x_3113_;
}
else
{
lean_dec_ref(v_a_u2082_3103_);
return v___x_3111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_mkAndS_spec__0___boxed(lean_object* v_f_3114_, lean_object* v_a_u2081_3115_, lean_object* v_a_u2082_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_mkAndS_spec__0(v_f_3114_, v_a_u2081_3115_, v_a_u2082_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkAndS(lean_object* v_p_3128_, lean_object* v_q_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = ((lean_object*)(l_Lean_Meta_Sym_mkAndS___closed__1));
v___x_3138_ = lean_box(0);
v___x_3139_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0___redArg(v___x_3137_, v___x_3138_, v_a_3131_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3141_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
v___x_3141_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_mkAndS_spec__0(v_a_3140_, v_p_3128_, v_q_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
return v___x_3141_;
}
else
{
lean_dec_ref(v_q_3129_);
lean_dec_ref(v_p_3128_);
return v___x_3139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkAndS___boxed(lean_object* v_p_3142_, lean_object* v_q_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lean_Meta_Sym_mkAndS(v_p_3142_, v_q_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec_ref(v_a_3146_);
lean_dec(v_a_3145_);
lean_dec_ref(v_a_3144_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkOrS(lean_object* v_p_3155_, lean_object* v_q_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = ((lean_object*)(l_Lean_Meta_Sym_mkOrS___closed__1));
v___x_3165_ = lean_box(0);
v___x_3166_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0___redArg(v___x_3164_, v___x_3165_, v_a_3158_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3168_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
lean_inc(v_a_3167_);
lean_dec_ref_known(v___x_3166_, 1);
v___x_3168_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_mkAndS_spec__0(v_a_3167_, v_p_3155_, v_q_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_);
return v___x_3168_;
}
else
{
lean_dec_ref(v_q_3156_);
lean_dec_ref(v_p_3155_);
return v___x_3166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkOrS___boxed(lean_object* v_p_3169_, lean_object* v_q_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_Lean_Meta_Sym_mkOrS(v_p_3169_, v_q_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_);
lean_dec(v_a_3176_);
lean_dec_ref(v_a_3175_);
lean_dec(v_a_3174_);
lean_dec_ref(v_a_3173_);
lean_dec(v_a_3172_);
lean_dec_ref(v_a_3171_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkExistsS(lean_object* v_u_3182_, lean_object* v_00_u03b1_3183_, lean_object* v_p_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3192_ = ((lean_object*)(l_Lean_Meta_Sym_mkExistsS___closed__1));
v___x_3193_ = lean_box(0);
v___x_3194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3194_, 0, v_u_3182_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Sym_mkNotS_spec__0___redArg(v___x_3192_, v___x_3194_, v_a_3186_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3197_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3195_, 1);
v___x_3197_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_mkAndS_spec__0(v_a_3196_, v_00_u03b1_3183_, v_p_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
return v___x_3197_;
}
else
{
lean_dec_ref(v_p_3184_);
lean_dec_ref(v_00_u03b1_3183_);
return v___x_3195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkExistsS___boxed(lean_object* v_u_3198_, lean_object* v_00_u03b1_3199_, lean_object* v_p_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_Meta_Sym_mkExistsS(v_u_3198_, v_00_u03b1_3199_, v_p_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
lean_dec(v_a_3206_);
lean_dec_ref(v_a_3205_);
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3203_);
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
return v_res_3208_;
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
