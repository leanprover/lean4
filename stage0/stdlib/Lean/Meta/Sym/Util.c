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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Meta_Sym_withLocalDeclS___redArg(lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_name_22_, uint8_t v_bi_23_, lean_object* v_type_24_, lean_object* v_k_25_){
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
LEAN_EXPORT void l_Lean_Meta_Sym_withLocalDeclS___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_19_ = stack[0].m_obj;
lean_object* v_inst_20_ = stack[1].m_obj;
lean_object* v_inst_21_ = stack[2].m_obj;
lean_object* v_name_22_ = stack[3].m_obj;
uint8_t v_bi_23_ = stack[4].m_num;
lean_object* v_type_24_ = stack[5].m_obj;
lean_object* v_k_25_ = stack[6].m_obj;
lean_object* v_res_32_;
v_res_32_ = l_Lean_Meta_Sym_withLocalDeclS___redArg(v_inst_19_, v_inst_20_, v_inst_21_, v_name_22_, v_bi_23_, v_type_24_, v_k_25_);
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___redArg___boxed(lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_name_36_, lean_object* v_bi_37_, lean_object* v_type_38_, lean_object* v_k_39_){
_start:
{
uint8_t v_bi_boxed_40_; lean_object* v_res_41_; 
v_bi_boxed_40_ = lean_unbox(v_bi_37_);
v_res_41_ = l_Lean_Meta_Sym_withLocalDeclS___redArg(v_inst_33_, v_inst_34_, v_inst_35_, v_name_36_, v_bi_boxed_40_, v_type_38_, v_k_39_);
return v_res_41_;
}
}
lean_object* l_Lean_Meta_Sym_withLocalDeclS(lean_object* v_n_42_, lean_object* v_00_u03b1_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_name_47_, uint8_t v_bi_48_, lean_object* v_type_49_, lean_object* v_k_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Meta_Sym_withLocalDeclS___redArg(v_inst_44_, v_inst_45_, v_inst_46_, v_name_47_, v_bi_48_, v_type_49_, v_k_50_);
return v___x_51_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_withLocalDeclS_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_44_ = stack[2].m_obj;
lean_object* v_inst_45_ = stack[3].m_obj;
lean_object* v_inst_46_ = stack[4].m_obj;
lean_object* v_name_47_ = stack[5].m_obj;
uint8_t v_bi_48_ = stack[6].m_num;
lean_object* v_type_49_ = stack[7].m_obj;
lean_object* v_k_50_ = stack[8].m_obj;
lean_object* v_res_52_;
v_res_52_ = l_Lean_Meta_Sym_withLocalDeclS(lean_box(0), lean_box(0), v_inst_44_, v_inst_45_, v_inst_46_, v_name_47_, v_bi_48_, v_type_49_, v_k_50_);
stack->m_obj
 = v_res_52_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___boxed(lean_object* v_n_53_, lean_object* v_00_u03b1_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_name_58_, lean_object* v_bi_59_, lean_object* v_type_60_, lean_object* v_k_61_){
_start:
{
uint8_t v_bi_boxed_62_; lean_object* v_res_63_; 
v_bi_boxed_62_ = lean_unbox(v_bi_59_);
v_res_63_ = l_Lean_Meta_Sym_withLocalDeclS(v_n_53_, v_00_u03b1_54_, v_inst_55_, v_inst_56_, v_inst_57_, v_name_58_, v_bi_boxed_62_, v_type_60_, v_k_61_);
return v_res_63_;
}
}
lean_object* l_Lean_Meta_Sym_withLetDeclS___redArg(lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_name_67_, lean_object* v_type_68_, lean_object* v_val_69_, lean_object* v_k_70_, uint8_t v_nondep_71_){
_start:
{
lean_object* v___x_72_; lean_object* v_toBind_73_; lean_object* v___f_74_; lean_object* v___f_75_; uint8_t v___x_76_; lean_object* v___x_77_; 
v___x_72_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM;
v_toBind_73_ = lean_ctor_get(v_inst_64_, 1);
v___f_74_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withLocalDeclS___redArg___lam__0), 2, 1);
lean_closure_set(v___f_74_, 0, v_k_70_);
lean_inc(v_toBind_73_);
v___f_75_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withLocalDeclS___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_75_, 0, v___x_72_);
lean_closure_set(v___f_75_, 1, v_inst_66_);
lean_closure_set(v___f_75_, 2, v_toBind_73_);
lean_closure_set(v___f_75_, 3, v___f_74_);
v___x_76_ = 0;
v___x_77_ = l_Lean_Meta_withLetDecl___redArg(v_inst_65_, v_inst_64_, v_name_67_, v_type_68_, v_val_69_, v___f_75_, v_nondep_71_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_withLetDeclS___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_64_ = stack[0].m_obj;
lean_object* v_inst_65_ = stack[1].m_obj;
lean_object* v_inst_66_ = stack[2].m_obj;
lean_object* v_name_67_ = stack[3].m_obj;
lean_object* v_type_68_ = stack[4].m_obj;
lean_object* v_val_69_ = stack[5].m_obj;
lean_object* v_k_70_ = stack[6].m_obj;
uint8_t v_nondep_71_ = stack[7].m_num;
lean_object* v_res_78_;
v_res_78_ = l_Lean_Meta_Sym_withLetDeclS___redArg(v_inst_64_, v_inst_65_, v_inst_66_, v_name_67_, v_type_68_, v_val_69_, v_k_70_, v_nondep_71_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___redArg___boxed(lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_name_82_, lean_object* v_type_83_, lean_object* v_val_84_, lean_object* v_k_85_, lean_object* v_nondep_86_){
_start:
{
uint8_t v_nondep_boxed_87_; lean_object* v_res_88_; 
v_nondep_boxed_87_ = lean_unbox(v_nondep_86_);
v_res_88_ = l_Lean_Meta_Sym_withLetDeclS___redArg(v_inst_79_, v_inst_80_, v_inst_81_, v_name_82_, v_type_83_, v_val_84_, v_k_85_, v_nondep_boxed_87_);
return v_res_88_;
}
}
lean_object* l_Lean_Meta_Sym_withLetDeclS(lean_object* v_n_89_, lean_object* v_00_u03b1_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_name_94_, lean_object* v_type_95_, lean_object* v_val_96_, lean_object* v_k_97_, uint8_t v_nondep_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Meta_Sym_withLetDeclS___redArg(v_inst_91_, v_inst_92_, v_inst_93_, v_name_94_, v_type_95_, v_val_96_, v_k_97_, v_nondep_98_);
return v___x_99_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_withLetDeclS_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_91_ = stack[2].m_obj;
lean_object* v_inst_92_ = stack[3].m_obj;
lean_object* v_inst_93_ = stack[4].m_obj;
lean_object* v_name_94_ = stack[5].m_obj;
lean_object* v_type_95_ = stack[6].m_obj;
lean_object* v_val_96_ = stack[7].m_obj;
lean_object* v_k_97_ = stack[8].m_obj;
uint8_t v_nondep_98_ = stack[9].m_num;
lean_object* v_res_100_;
v_res_100_ = l_Lean_Meta_Sym_withLetDeclS(lean_box(0), lean_box(0), v_inst_91_, v_inst_92_, v_inst_93_, v_name_94_, v_type_95_, v_val_96_, v_k_97_, v_nondep_98_);
stack->m_obj
 = v_res_100_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLetDeclS___boxed(lean_object* v_n_101_, lean_object* v_00_u03b1_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_name_106_, lean_object* v_type_107_, lean_object* v_val_108_, lean_object* v_k_109_, lean_object* v_nondep_110_){
_start:
{
uint8_t v_nondep_boxed_111_; lean_object* v_res_112_; 
v_nondep_boxed_111_ = lean_unbox(v_nondep_110_);
v_res_112_ = l_Lean_Meta_Sym_withLetDeclS(v_n_101_, v_00_u03b1_102_, v_inst_103_, v_inst_104_, v_inst_105_, v_name_106_, v_type_107_, v_val_108_, v_k_109_, v_nondep_boxed_111_);
return v_res_112_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_113_;
}
}
lean_object* l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0(lean_object* v_msg_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_452__overap_123_; lean_object* v___x_124_; 
v___x_122_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___closed__0);
v___x_452__overap_123_ = lean_panic_fn_borrowed(v___x_122_, v_msg_114_);
lean_inc(v___y_120_);
lean_inc_ref(v___y_119_);
lean_inc(v___y_118_);
lean_inc_ref(v___y_117_);
lean_inc(v___y_116_);
lean_inc_ref(v___y_115_);
v___x_124_ = lean_apply_7(v___x_452__overap_123_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, lean_box(0));
return v___x_124_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_114_ = stack[0].m_obj;
lean_object* v___y_115_ = stack[1].m_obj;
lean_object* v___y_116_ = stack[2].m_obj;
lean_object* v___y_117_ = stack[3].m_obj;
lean_object* v___y_118_ = stack[4].m_obj;
lean_object* v___y_119_ = stack[5].m_obj;
lean_object* v___y_120_ = stack[6].m_obj;
lean_object* v_res_125_;
v_res_125_ = l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0(v_msg_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
stack->m_obj
 = v_res_125_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0___boxed(lean_object* v_msg_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0(v_msg_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_134_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(lean_object* v_e_135_, lean_object* v___y_136_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = l_Lean_Expr_hasMVar(v_e_135_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v_e_135_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v_mctx_141_; lean_object* v___x_142_; lean_object* v_fst_143_; lean_object* v_snd_144_; lean_object* v___x_145_; lean_object* v_cache_146_; lean_object* v_zetaDeltaFVarIds_147_; lean_object* v_postponed_148_; lean_object* v_diag_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_158_; 
v___x_140_ = lean_st_ref_get(v___y_136_);
v_mctx_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc_ref(v_mctx_141_);
lean_dec(v___x_140_);
v___x_142_ = l_Lean_instantiateMVarsCore(v_mctx_141_, v_e_135_);
v_fst_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_fst_143_);
v_snd_144_ = lean_ctor_get(v___x_142_, 1);
lean_inc(v_snd_144_);
lean_dec_ref(v___x_142_);
v___x_145_ = lean_st_ref_take(v___y_136_);
v_cache_146_ = lean_ctor_get(v___x_145_, 1);
v_zetaDeltaFVarIds_147_ = lean_ctor_get(v___x_145_, 2);
v_postponed_148_ = lean_ctor_get(v___x_145_, 3);
v_diag_149_ = lean_ctor_get(v___x_145_, 4);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v___x_145_, 0);
lean_dec(v_unused_159_);
v___x_151_ = v___x_145_;
v_isShared_152_ = v_isSharedCheck_158_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_diag_149_);
lean_inc(v_postponed_148_);
lean_inc(v_zetaDeltaFVarIds_147_);
lean_inc(v_cache_146_);
lean_dec(v___x_145_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_158_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v_snd_144_);
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_snd_144_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_cache_146_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_zetaDeltaFVarIds_147_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v_postponed_148_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v_diag_149_);
v___x_154_ = v_reuseFailAlloc_157_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_st_ref_put(v___y_136_, v___x_154_);
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v_fst_143_);
return v___x_156_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_135_ = stack[0].m_obj;
lean_object* v___y_136_ = stack[1].m_obj;
lean_object* v_res_160_;
v_res_160_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(v_e_135_, v___y_136_);
stack->m_obj
 = v_res_160_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg___boxed(lean_object* v_e_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(v_e_161_, v___y_162_);
lean_dec(v___y_162_);
return v_res_164_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1(lean_object* v_e_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(v_e_165_, v___y_169_);
return v___x_173_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_165_ = stack[0].m_obj;
lean_object* v___y_166_ = stack[1].m_obj;
lean_object* v___y_167_ = stack[2].m_obj;
lean_object* v___y_168_ = stack[3].m_obj;
lean_object* v___y_169_ = stack[4].m_obj;
lean_object* v___y_170_ = stack[5].m_obj;
lean_object* v___y_171_ = stack[6].m_obj;
lean_object* v_res_174_;
v_res_174_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1(v_e_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___boxed(lean_object* v_e_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1(v_e_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_183_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_preprocessExpr___closed__3(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_187_ = ((lean_object*)(l_Lean_Meta_Sym_preprocessExpr___closed__2));
v___x_188_ = lean_unsigned_to_nat(2u);
v___x_189_ = lean_unsigned_to_nat(36u);
v___x_190_ = ((lean_object*)(l_Lean_Meta_Sym_preprocessExpr___closed__1));
v___x_191_ = ((lean_object*)(l_Lean_Meta_Sym_preprocessExpr___closed__0));
v___x_192_ = l_mkPanicMessageWithDecl(v___x_191_, v___x_190_, v___x_189_, v___x_188_, v___x_187_);
return v___x_192_;
}
}
lean_object* l_Lean_Meta_Sym_preprocessExpr(lean_object* v_e_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_194_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; uint8_t v_enforceUnfoldReducible_203_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_201_, 1);
v_enforceUnfoldReducible_203_ = lean_ctor_get_uint8(v_a_202_, 1);
lean_dec(v_a_202_);
if (v_enforceUnfoldReducible_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec_ref(v_e_193_);
v___x_204_ = lean_obj_once(&l_Lean_Meta_Sym_preprocessExpr___closed__3, &l_Lean_Meta_Sym_preprocessExpr___closed__3_once, _init_l_Lean_Meta_Sym_preprocessExpr___closed__3);
v___x_205_ = l_panic___at___00Lean_Meta_Sym_preprocessExpr_spec__0(v___x_204_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
return v___x_205_;
}
else
{
lean_object* v___x_206_; lean_object* v_a_207_; lean_object* v___x_208_; 
v___x_206_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_preprocessExpr_spec__1___redArg(v_e_193_, v_a_197_);
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref(v___x_206_);
v___x_208_ = l_Lean_Meta_Sym_shareCommon(v_a_207_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
return v___x_208_;
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
lean_dec_ref(v_e_193_);
v_a_209_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_201_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_201_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_preprocessExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_193_ = stack[0].m_obj;
lean_object* v_a_194_ = stack[1].m_obj;
lean_object* v_a_195_ = stack[2].m_obj;
lean_object* v_a_196_ = stack[3].m_obj;
lean_object* v_a_197_ = stack[4].m_obj;
lean_object* v_a_198_ = stack[5].m_obj;
lean_object* v_a_199_ = stack[6].m_obj;
lean_object* v_res_217_;
v_res_217_ = l_Lean_Meta_Sym_preprocessExpr(v_e_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessExpr___boxed(lean_object* v_e_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Meta_Sym_preprocessExpr(v_e_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_227_, lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
lean_object* v_ks_231_; lean_object* v_vs_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_256_; 
v_ks_231_ = lean_ctor_get(v_x_227_, 0);
v_vs_232_ = lean_ctor_get(v_x_227_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_256_ == 0)
{
v___x_234_ = v_x_227_;
v_isShared_235_ = v_isSharedCheck_256_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_vs_232_);
lean_inc(v_ks_231_);
lean_dec(v_x_227_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_256_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_array_get_size(v_ks_231_);
v___x_237_ = lean_nat_dec_lt(v_x_228_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
lean_dec(v_x_228_);
v___x_238_ = lean_array_push(v_ks_231_, v_x_229_);
v___x_239_ = lean_array_push(v_vs_232_, v_x_230_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_239_);
lean_ctor_set(v___x_234_, 0, v___x_238_);
v___x_241_ = v___x_234_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
else
{
lean_object* v_k_x27_243_; uint8_t v___x_244_; 
v_k_x27_243_ = lean_array_fget_borrowed(v_ks_231_, v_x_228_);
v___x_244_ = l_Lean_instBEqFVarId_beq(v_x_229_, v_k_x27_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_246_; 
if (v_isShared_235_ == 0)
{
v___x_246_ = v___x_234_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_ks_231_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_vs_232_);
v___x_246_ = v_reuseFailAlloc_250_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_unsigned_to_nat(1u);
v___x_248_ = lean_nat_add(v_x_228_, v___x_247_);
lean_dec(v_x_228_);
v_x_227_ = v___x_246_;
v_x_228_ = v___x_248_;
goto _start;
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_251_ = lean_array_fset(v_ks_231_, v_x_228_, v_x_229_);
v___x_252_ = lean_array_fset(v_vs_232_, v_x_228_, v_x_230_);
lean_dec(v_x_228_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_252_);
lean_ctor_set(v___x_234_, 0, v___x_251_);
v___x_254_ = v___x_234_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(lean_object* v_n_257_, lean_object* v_k_258_, lean_object* v_v_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_n_257_, v___x_260_, v_k_258_, v_v_259_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_262_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(lean_object* v_x_263_, size_t v_x_264_, size_t v_x_265_, lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_object* v_es_268_; size_t v___x_269_; size_t v___x_270_; lean_object* v_j_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_es_268_ = lean_ctor_get(v_x_263_, 0);
v___x_269_ = ((size_t)31ULL);
v___x_270_ = lean_usize_land(v_x_264_, v___x_269_);
v_j_271_ = lean_usize_to_nat(v___x_270_);
v___x_272_ = lean_array_get_size(v_es_268_);
v___x_273_ = lean_nat_dec_lt(v_j_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_dec(v_j_271_);
lean_dec(v_x_267_);
lean_dec(v_x_266_);
return v_x_263_;
}
else
{
lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_312_; 
lean_inc_ref(v_es_268_);
v_isSharedCheck_312_ = !lean_is_exclusive(v_x_263_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; 
v_unused_313_ = lean_ctor_get(v_x_263_, 0);
lean_dec(v_unused_313_);
v___x_275_ = v_x_263_;
v_isShared_276_ = v_isSharedCheck_312_;
goto v_resetjp_274_;
}
else
{
lean_dec(v_x_263_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_312_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v_v_277_; lean_object* v___x_278_; lean_object* v_xs_x27_279_; lean_object* v___y_281_; 
v_v_277_ = lean_array_fget(v_es_268_, v_j_271_);
v___x_278_ = lean_box(0);
v_xs_x27_279_ = lean_array_fset(v_es_268_, v_j_271_, v___x_278_);
switch(lean_obj_tag(v_v_277_))
{
case 0:
{
lean_object* v_key_286_; lean_object* v_val_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_297_; 
v_key_286_ = lean_ctor_get(v_v_277_, 0);
v_val_287_ = lean_ctor_get(v_v_277_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v_v_277_);
if (v_isSharedCheck_297_ == 0)
{
v___x_289_ = v_v_277_;
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_val_287_);
lean_inc(v_key_286_);
lean_dec(v_v_277_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
uint8_t v___x_291_; 
v___x_291_ = l_Lean_instBEqFVarId_beq(v_x_266_, v_key_286_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_del_object(v___x_289_);
v___x_292_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_286_, v_val_287_, v_x_266_, v_x_267_);
v___x_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
v___y_281_ = v___x_293_;
goto v___jp_280_;
}
else
{
lean_object* v___x_295_; 
lean_dec(v_val_287_);
lean_dec(v_key_286_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v_x_267_);
lean_ctor_set(v___x_289_, 0, v_x_266_);
v___x_295_ = v___x_289_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_x_266_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_x_267_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
v___y_281_ = v___x_295_;
goto v___jp_280_;
}
}
}
}
case 1:
{
lean_object* v_node_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_310_; 
v_node_298_ = lean_ctor_get(v_v_277_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v_v_277_);
if (v_isSharedCheck_310_ == 0)
{
v___x_300_ = v_v_277_;
v_isShared_301_ = v_isSharedCheck_310_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_node_298_);
lean_dec(v_v_277_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_310_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
size_t v___x_302_; size_t v___x_303_; size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_302_ = ((size_t)5ULL);
v___x_303_ = lean_usize_shift_right(v_x_264_, v___x_302_);
v___x_304_ = ((size_t)1ULL);
v___x_305_ = lean_usize_add(v_x_265_, v___x_304_);
v___x_306_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_node_298_, v___x_303_, v___x_305_, v_x_266_, v_x_267_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_306_);
v___x_308_ = v___x_300_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
v___y_281_ = v___x_308_;
goto v___jp_280_;
}
}
}
default: 
{
lean_object* v___x_311_; 
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v_x_266_);
lean_ctor_set(v___x_311_, 1, v_x_267_);
v___y_281_ = v___x_311_;
goto v___jp_280_;
}
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_282_ = lean_array_fset(v_xs_x27_279_, v_j_271_, v___y_281_);
lean_dec(v_j_271_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_282_);
v___x_284_ = v___x_275_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
else
{
lean_object* v_ks_314_; lean_object* v_vs_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_333_; 
v_ks_314_ = lean_ctor_get(v_x_263_, 0);
v_vs_315_ = lean_ctor_get(v_x_263_, 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_263_);
if (v_isSharedCheck_333_ == 0)
{
v___x_317_ = v_x_263_;
v_isShared_318_ = v_isSharedCheck_333_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_vs_315_);
lean_inc(v_ks_314_);
lean_dec(v_x_263_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_333_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_ks_314_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_vs_315_);
v___x_320_ = v_reuseFailAlloc_332_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v_newNode_321_; size_t v___x_322_; uint8_t v___x_323_; 
v_newNode_321_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v___x_320_, v_x_266_, v_x_267_);
v___x_322_ = ((size_t)7ULL);
v___x_323_ = lean_usize_dec_le(v___x_322_, v_x_265_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_324_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_321_);
v___x_325_ = lean_unsigned_to_nat(4u);
v___x_326_ = lean_nat_dec_lt(v___x_324_, v___x_325_);
lean_dec(v___x_324_);
if (v___x_326_ == 0)
{
lean_object* v_ks_327_; lean_object* v_vs_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_ks_327_ = lean_ctor_get(v_newNode_321_, 0);
lean_inc_ref(v_ks_327_);
v_vs_328_ = lean_ctor_get(v_newNode_321_, 1);
lean_inc_ref(v_vs_328_);
lean_dec_ref(v_newNode_321_);
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0);
v___x_331_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_x_265_, v_ks_327_, v_vs_328_, v___x_329_, v___x_330_);
lean_dec_ref(v_vs_328_);
lean_dec_ref(v_ks_327_);
return v___x_331_;
}
else
{
return v_newNode_321_;
}
}
else
{
return v_newNode_321_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_263_ = stack[0].m_obj;
size_t v_x_264_ = stack[1].m_num;
size_t v_x_265_ = stack[2].m_num;
lean_object* v_x_266_ = stack[3].m_obj;
lean_object* v_x_267_ = stack[4].m_obj;
lean_object* v_res_334_;
v_res_334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_263_, v_x_264_, v_x_265_, v_x_266_, v_x_267_);
stack->m_obj
 = v_res_334_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(size_t v_depth_335_, lean_object* v_keys_336_, lean_object* v_vals_337_, lean_object* v_i_338_, lean_object* v_entries_339_){
_start:
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = lean_array_get_size(v_keys_336_);
v___x_341_ = lean_nat_dec_lt(v_i_338_, v___x_340_);
if (v___x_341_ == 0)
{
lean_dec(v_i_338_);
return v_entries_339_;
}
else
{
lean_object* v_k_342_; lean_object* v_v_343_; uint64_t v___x_344_; size_t v_h_345_; size_t v___x_346_; lean_object* v___x_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; size_t v_h_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_k_342_ = lean_array_fget_borrowed(v_keys_336_, v_i_338_);
v_v_343_ = lean_array_fget_borrowed(v_vals_337_, v_i_338_);
v___x_344_ = l_Lean_instHashableFVarId_hash(v_k_342_);
v_h_345_ = lean_uint64_to_usize(v___x_344_);
v___x_346_ = ((size_t)5ULL);
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_sub(v_depth_335_, v___x_348_);
v___x_350_ = lean_usize_mul(v___x_346_, v___x_349_);
v_h_351_ = lean_usize_shift_right(v_h_345_, v___x_350_);
v___x_352_ = lean_nat_add(v_i_338_, v___x_347_);
lean_dec(v_i_338_);
lean_inc(v_v_343_);
lean_inc(v_k_342_);
v___x_353_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_entries_339_, v_h_351_, v_depth_335_, v_k_342_, v_v_343_);
v_i_338_ = v___x_352_;
v_entries_339_ = v___x_353_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_335_ = stack[0].m_num;
lean_object* v_keys_336_ = stack[1].m_obj;
lean_object* v_vals_337_ = stack[2].m_obj;
lean_object* v_i_338_ = stack[3].m_obj;
lean_object* v_entries_339_ = stack[4].m_obj;
lean_object* v_res_355_;
v_res_355_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_335_, v_keys_336_, v_vals_337_, v_i_338_, v_entries_339_);
stack->m_obj
 = v_res_355_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_356_, lean_object* v_keys_357_, lean_object* v_vals_358_, lean_object* v_i_359_, lean_object* v_entries_360_){
_start:
{
size_t v_depth_boxed_361_; lean_object* v_res_362_; 
v_depth_boxed_361_ = lean_unbox_usize(v_depth_356_);
lean_dec(v_depth_356_);
v_res_362_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_boxed_361_, v_keys_357_, v_vals_358_, v_i_359_, v_entries_360_);
lean_dec_ref(v_vals_358_);
lean_dec_ref(v_keys_357_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___boxed(lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
size_t v_x_9234__boxed_368_; size_t v_x_9235__boxed_369_; lean_object* v_res_370_; 
v_x_9234__boxed_368_ = lean_unbox_usize(v_x_364_);
lean_dec(v_x_364_);
v_x_9235__boxed_369_ = lean_unbox_usize(v_x_365_);
lean_dec(v_x_365_);
v_res_370_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_363_, v_x_9234__boxed_368_, v_x_9235__boxed_369_, v_x_366_, v_x_367_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v_x_373_){
_start:
{
uint64_t v___x_374_; size_t v___x_375_; size_t v___x_376_; lean_object* v___x_377_; 
v___x_374_ = l_Lean_instHashableFVarId_hash(v_x_372_);
v___x_375_ = lean_uint64_to_usize(v___x_374_);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_371_, v___x_375_, v___x_376_, v_x_372_, v_x_373_);
return v___x_377_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(lean_object* v_as_378_, size_t v_sz_379_, size_t v_i_380_, lean_object* v_b_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = lean_usize_dec_lt(v_i_380_, v_sz_379_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v_b_381_);
return v___x_390_;
}
else
{
lean_object* v_snd_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_496_; 
v_snd_391_ = lean_ctor_get(v_b_381_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_b_381_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v_b_381_, 0);
lean_dec(v_unused_497_);
v___x_393_ = v_b_381_;
v_isShared_394_ = v_isSharedCheck_496_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_snd_391_);
lean_dec(v_b_381_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_496_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v_a_397_; lean_object* v_a_404_; 
v___x_395_ = lean_box(0);
v_a_404_ = lean_array_uget(v_as_378_, v_i_380_);
if (lean_obj_tag(v_a_404_) == 0)
{
v_a_397_ = v_snd_391_;
goto v___jp_396_;
}
else
{
lean_object* v_snd_405_; lean_object* v_val_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_495_; 
v_snd_405_ = lean_ctor_get(v_snd_391_, 1);
lean_inc(v_snd_405_);
v_val_406_ = lean_ctor_get(v_a_404_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_a_404_);
if (v_isSharedCheck_495_ == 0)
{
v___x_408_ = v_a_404_;
v_isShared_409_ = v_isSharedCheck_495_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_val_406_);
lean_dec(v_a_404_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_495_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_fst_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_493_; 
v_fst_410_ = lean_ctor_get(v_snd_391_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v_snd_391_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v_snd_391_, 1);
lean_dec(v_unused_494_);
v___x_412_ = v_snd_391_;
v_isShared_413_ = v_isSharedCheck_493_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_fst_410_);
lean_dec(v_snd_391_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_493_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_492_; 
v_fst_414_ = lean_ctor_get(v_snd_405_, 0);
v_snd_415_ = lean_ctor_get(v_snd_405_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_snd_405_);
if (v_isSharedCheck_492_ == 0)
{
v___x_417_ = v_snd_405_;
v_isShared_418_ = v_isSharedCheck_492_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_snd_415_);
lean_inc(v_fst_414_);
lean_dec(v_snd_405_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_492_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_decl_420_; 
if (lean_obj_tag(v_val_406_) == 0)
{
lean_object* v_fvarId_435_; lean_object* v_userName_436_; lean_object* v_type_437_; uint8_t v_bi_438_; uint8_t v_kind_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_456_; 
v_fvarId_435_ = lean_ctor_get(v_val_406_, 1);
v_userName_436_ = lean_ctor_get(v_val_406_, 2);
v_type_437_ = lean_ctor_get(v_val_406_, 3);
v_bi_438_ = lean_ctor_get_uint8(v_val_406_, sizeof(void*)*4);
v_kind_439_ = lean_ctor_get_uint8(v_val_406_, sizeof(void*)*4 + 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_val_406_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v_val_406_, 0);
lean_dec(v_unused_457_);
v___x_441_ = v_val_406_;
v_isShared_442_ = v_isSharedCheck_456_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_type_437_);
lean_inc(v_userName_436_);
lean_inc(v_fvarId_435_);
lean_dec(v_val_406_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_456_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Meta_Sym_preprocessExpr(v_type_437_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
lean_inc(v_snd_415_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 3, v_a_444_);
lean_ctor_set(v___x_441_, 0, v_snd_415_);
v___x_446_ = v___x_441_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_snd_415_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_fvarId_435_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_userName_436_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_a_444_);
lean_ctor_set_uint8(v_reuseFailAlloc_447_, sizeof(void*)*4, v_bi_438_);
lean_ctor_set_uint8(v_reuseFailAlloc_447_, sizeof(void*)*4 + 1, v_kind_439_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
v_decl_420_ = v___x_446_;
goto v___jp_419_;
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_del_object(v___x_441_);
lean_dec(v_userName_436_);
lean_dec(v_fvarId_435_);
lean_del_object(v___x_417_);
lean_dec(v_snd_415_);
lean_dec(v_fst_414_);
lean_del_object(v___x_412_);
lean_dec(v_fst_410_);
lean_del_object(v___x_408_);
lean_del_object(v___x_393_);
v_a_448_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_443_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_443_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
else
{
lean_object* v_fvarId_458_; lean_object* v_userName_459_; lean_object* v_type_460_; lean_object* v_value_461_; uint8_t v_nondep_462_; uint8_t v_kind_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_490_; 
v_fvarId_458_ = lean_ctor_get(v_val_406_, 1);
v_userName_459_ = lean_ctor_get(v_val_406_, 2);
v_type_460_ = lean_ctor_get(v_val_406_, 3);
v_value_461_ = lean_ctor_get(v_val_406_, 4);
v_nondep_462_ = lean_ctor_get_uint8(v_val_406_, sizeof(void*)*5);
v_kind_463_ = lean_ctor_get_uint8(v_val_406_, sizeof(void*)*5 + 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v_val_406_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v_val_406_, 0);
lean_dec(v_unused_491_);
v___x_465_ = v_val_406_;
v_isShared_466_ = v_isSharedCheck_490_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_value_461_);
lean_inc(v_type_460_);
lean_inc(v_userName_459_);
lean_inc(v_fvarId_458_);
lean_dec(v_val_406_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_490_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Meta_Sym_preprocessExpr(v_type_460_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_469_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
v___x_469_ = l_Lean_Meta_Sym_preprocessExpr(v_value_461_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
lean_inc(v_snd_415_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 4, v_a_470_);
lean_ctor_set(v___x_465_, 3, v_a_468_);
lean_ctor_set(v___x_465_, 0, v_snd_415_);
v___x_472_ = v___x_465_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_snd_415_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_fvarId_458_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_userName_459_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_a_468_);
lean_ctor_set(v_reuseFailAlloc_473_, 4, v_a_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, sizeof(void*)*5, v_nondep_462_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, sizeof(void*)*5 + 1, v_kind_463_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
v_decl_420_ = v___x_472_;
goto v___jp_419_;
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v_a_468_);
lean_del_object(v___x_465_);
lean_dec(v_userName_459_);
lean_dec(v_fvarId_458_);
lean_del_object(v___x_417_);
lean_dec(v_snd_415_);
lean_dec(v_fst_414_);
lean_del_object(v___x_412_);
lean_dec(v_fst_410_);
lean_del_object(v___x_408_);
lean_del_object(v___x_393_);
v_a_474_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_469_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_469_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_del_object(v___x_465_);
lean_dec_ref(v_value_461_);
lean_dec(v_userName_459_);
lean_dec(v_fvarId_458_);
lean_del_object(v___x_417_);
lean_dec(v_snd_415_);
lean_dec(v_fst_414_);
lean_del_object(v___x_412_);
lean_dec(v_fst_410_);
lean_del_object(v___x_408_);
lean_del_object(v___x_393_);
v_a_482_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_467_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_467_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
v___jp_419_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v_snd_415_, v___x_421_);
lean_dec(v_snd_415_);
lean_inc_ref(v_decl_420_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v_decl_420_);
v___x_424_ = v___x_408_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_decl_420_);
v___x_424_ = v_reuseFailAlloc_434_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_425_ = l_Lean_PersistentArray_push___redArg(v_fst_414_, v___x_424_);
v___x_426_ = l_Lean_LocalDecl_fvarId(v_decl_420_);
v___x_427_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_410_, v___x_426_, v_decl_420_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___x_422_);
lean_ctor_set(v___x_417_, 0, v___x_425_);
v___x_429_ = v___x_417_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v___x_422_);
v___x_429_ = v_reuseFailAlloc_433_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_431_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v___x_429_);
lean_ctor_set(v___x_412_, 0, v___x_427_);
v___x_431_ = v___x_412_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
v_a_397_ = v___x_431_;
goto v___jp_396_;
}
}
}
}
}
}
}
}
v___jp_396_:
{
lean_object* v___x_399_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v_a_397_);
lean_ctor_set(v___x_393_, 0, v___x_395_);
v___x_399_ = v___x_393_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_a_397_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
size_t v___x_400_; size_t v___x_401_; 
v___x_400_ = ((size_t)1ULL);
v___x_401_ = lean_usize_add(v_i_380_, v___x_400_);
v_i_380_ = v___x_401_;
v_b_381_ = v___x_399_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_378_ = stack[0].m_obj;
size_t v_sz_379_ = stack[1].m_num;
size_t v_i_380_ = stack[2].m_num;
lean_object* v_b_381_ = stack[3].m_obj;
lean_object* v___y_382_ = stack[4].m_obj;
lean_object* v___y_383_ = stack[5].m_obj;
lean_object* v___y_384_ = stack[6].m_obj;
lean_object* v___y_385_ = stack[7].m_obj;
lean_object* v___y_386_ = stack[8].m_obj;
lean_object* v___y_387_ = stack[9].m_obj;
lean_object* v_res_498_;
v_res_498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_378_, v_sz_379_, v_i_380_, v_b_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
stack->m_obj
 = v_res_498_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_as_499_, lean_object* v_sz_500_, lean_object* v_i_501_, lean_object* v_b_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
size_t v_sz_boxed_510_; size_t v_i_boxed_511_; lean_object* v_res_512_; 
v_sz_boxed_510_ = lean_unbox_usize(v_sz_500_);
lean_dec(v_sz_500_);
v_i_boxed_511_ = lean_unbox_usize(v_i_501_);
lean_dec(v_i_501_);
v_res_512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_499_, v_sz_boxed_510_, v_i_boxed_511_, v_b_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec_ref(v_as_499_);
return v_res_512_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(lean_object* v_as_513_, size_t v_sz_514_, size_t v_i_515_, lean_object* v_b_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v___x_524_; 
v___x_524_ = lean_usize_dec_lt(v_i_515_, v_sz_514_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v_b_516_);
return v___x_525_;
}
else
{
lean_object* v_snd_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_631_; 
v_snd_526_ = lean_ctor_get(v_b_516_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_b_516_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v_b_516_, 0);
lean_dec(v_unused_632_);
v___x_528_ = v_b_516_;
v_isShared_529_ = v_isSharedCheck_631_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_snd_526_);
lean_dec(v_b_516_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_631_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v_a_532_; lean_object* v_a_539_; 
v___x_530_ = lean_box(0);
v_a_539_ = lean_array_uget(v_as_513_, v_i_515_);
if (lean_obj_tag(v_a_539_) == 0)
{
v_a_532_ = v_snd_526_;
goto v___jp_531_;
}
else
{
lean_object* v_snd_540_; lean_object* v_val_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_630_; 
v_snd_540_ = lean_ctor_get(v_snd_526_, 1);
lean_inc(v_snd_540_);
v_val_541_ = lean_ctor_get(v_a_539_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_a_539_);
if (v_isSharedCheck_630_ == 0)
{
v___x_543_ = v_a_539_;
v_isShared_544_ = v_isSharedCheck_630_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_val_541_);
lean_dec(v_a_539_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_630_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v_fst_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_628_; 
v_fst_545_ = lean_ctor_get(v_snd_526_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v_snd_526_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v_snd_526_, 1);
lean_dec(v_unused_629_);
v___x_547_ = v_snd_526_;
v_isShared_548_ = v_isSharedCheck_628_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_fst_545_);
lean_dec(v_snd_526_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_628_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v_fst_549_; lean_object* v_snd_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_627_; 
v_fst_549_ = lean_ctor_get(v_snd_540_, 0);
v_snd_550_ = lean_ctor_get(v_snd_540_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_snd_540_);
if (v_isSharedCheck_627_ == 0)
{
v___x_552_ = v_snd_540_;
v_isShared_553_ = v_isSharedCheck_627_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_snd_550_);
lean_inc(v_fst_549_);
lean_dec(v_snd_540_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_627_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v_decl_555_; 
if (lean_obj_tag(v_val_541_) == 0)
{
lean_object* v_fvarId_570_; lean_object* v_userName_571_; lean_object* v_type_572_; uint8_t v_bi_573_; uint8_t v_kind_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_591_; 
v_fvarId_570_ = lean_ctor_get(v_val_541_, 1);
v_userName_571_ = lean_ctor_get(v_val_541_, 2);
v_type_572_ = lean_ctor_get(v_val_541_, 3);
v_bi_573_ = lean_ctor_get_uint8(v_val_541_, sizeof(void*)*4);
v_kind_574_ = lean_ctor_get_uint8(v_val_541_, sizeof(void*)*4 + 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_val_541_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v_val_541_, 0);
lean_dec(v_unused_592_);
v___x_576_ = v_val_541_;
v_isShared_577_ = v_isSharedCheck_591_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_type_572_);
lean_inc(v_userName_571_);
lean_inc(v_fvarId_570_);
lean_dec(v_val_541_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_591_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Meta_Sym_preprocessExpr(v_type_572_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
lean_inc(v_snd_550_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 3, v_a_579_);
lean_ctor_set(v___x_576_, 0, v_snd_550_);
v___x_581_ = v___x_576_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_snd_550_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_fvarId_570_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_userName_571_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v_a_579_);
lean_ctor_set_uint8(v_reuseFailAlloc_582_, sizeof(void*)*4, v_bi_573_);
lean_ctor_set_uint8(v_reuseFailAlloc_582_, sizeof(void*)*4 + 1, v_kind_574_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
v_decl_555_ = v___x_581_;
goto v___jp_554_;
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_del_object(v___x_576_);
lean_dec(v_userName_571_);
lean_dec(v_fvarId_570_);
lean_del_object(v___x_552_);
lean_dec(v_snd_550_);
lean_dec(v_fst_549_);
lean_del_object(v___x_547_);
lean_dec(v_fst_545_);
lean_del_object(v___x_543_);
lean_del_object(v___x_528_);
v_a_583_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_578_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_578_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
else
{
lean_object* v_fvarId_593_; lean_object* v_userName_594_; lean_object* v_type_595_; lean_object* v_value_596_; uint8_t v_nondep_597_; uint8_t v_kind_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_625_; 
v_fvarId_593_ = lean_ctor_get(v_val_541_, 1);
v_userName_594_ = lean_ctor_get(v_val_541_, 2);
v_type_595_ = lean_ctor_get(v_val_541_, 3);
v_value_596_ = lean_ctor_get(v_val_541_, 4);
v_nondep_597_ = lean_ctor_get_uint8(v_val_541_, sizeof(void*)*5);
v_kind_598_ = lean_ctor_get_uint8(v_val_541_, sizeof(void*)*5 + 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_val_541_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v_val_541_, 0);
lean_dec(v_unused_626_);
v___x_600_ = v_val_541_;
v_isShared_601_ = v_isSharedCheck_625_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_value_596_);
lean_inc(v_type_595_);
lean_inc(v_userName_594_);
lean_inc(v_fvarId_593_);
lean_dec(v_val_541_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_625_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Meta_Sym_preprocessExpr(v_type_595_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_604_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v___x_604_ = l_Lean_Meta_Sym_preprocessExpr(v_value_596_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
lean_inc(v_snd_550_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 4, v_a_605_);
lean_ctor_set(v___x_600_, 3, v_a_603_);
lean_ctor_set(v___x_600_, 0, v_snd_550_);
v___x_607_ = v___x_600_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_snd_550_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_fvarId_593_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_userName_594_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_a_603_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_a_605_);
lean_ctor_set_uint8(v_reuseFailAlloc_608_, sizeof(void*)*5, v_nondep_597_);
lean_ctor_set_uint8(v_reuseFailAlloc_608_, sizeof(void*)*5 + 1, v_kind_598_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
v_decl_555_ = v___x_607_;
goto v___jp_554_;
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec(v_a_603_);
lean_del_object(v___x_600_);
lean_dec(v_userName_594_);
lean_dec(v_fvarId_593_);
lean_del_object(v___x_552_);
lean_dec(v_snd_550_);
lean_dec(v_fst_549_);
lean_del_object(v___x_547_);
lean_dec(v_fst_545_);
lean_del_object(v___x_543_);
lean_del_object(v___x_528_);
v_a_609_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_604_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_604_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_del_object(v___x_600_);
lean_dec_ref(v_value_596_);
lean_dec(v_userName_594_);
lean_dec(v_fvarId_593_);
lean_del_object(v___x_552_);
lean_dec(v_snd_550_);
lean_dec(v_fst_549_);
lean_del_object(v___x_547_);
lean_dec(v_fst_545_);
lean_del_object(v___x_543_);
lean_del_object(v___x_528_);
v_a_617_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_602_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_602_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
v___jp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_add(v_snd_550_, v___x_556_);
lean_dec(v_snd_550_);
lean_inc_ref(v_decl_555_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v_decl_555_);
v___x_559_ = v___x_543_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_decl_555_);
v___x_559_ = v_reuseFailAlloc_569_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_560_ = l_Lean_PersistentArray_push___redArg(v_fst_549_, v___x_559_);
v___x_561_ = l_Lean_LocalDecl_fvarId(v_decl_555_);
v___x_562_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_545_, v___x_561_, v_decl_555_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_557_);
lean_ctor_set(v___x_552_, 0, v___x_560_);
v___x_564_ = v___x_552_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_557_);
v___x_564_ = v_reuseFailAlloc_568_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_566_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 1, v___x_564_);
lean_ctor_set(v___x_547_, 0, v___x_562_);
v___x_566_ = v___x_547_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
v_a_532_ = v___x_566_;
goto v___jp_531_;
}
}
}
}
}
}
}
}
v___jp_531_:
{
lean_object* v___x_534_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 1, v_a_532_);
lean_ctor_set(v___x_528_, 0, v___x_530_);
v___x_534_ = v___x_528_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_a_532_);
v___x_534_ = v_reuseFailAlloc_538_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
size_t v___x_535_; size_t v___x_536_; lean_object* v___x_537_; 
v___x_535_ = ((size_t)1ULL);
v___x_536_ = lean_usize_add(v_i_515_, v___x_535_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_513_, v_sz_514_, v___x_536_, v___x_534_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
return v___x_537_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_513_ = stack[0].m_obj;
size_t v_sz_514_ = stack[1].m_num;
size_t v_i_515_ = stack[2].m_num;
lean_object* v_b_516_ = stack[3].m_obj;
lean_object* v___y_517_ = stack[4].m_obj;
lean_object* v___y_518_ = stack[5].m_obj;
lean_object* v___y_519_ = stack[6].m_obj;
lean_object* v___y_520_ = stack[7].m_obj;
lean_object* v___y_521_ = stack[8].m_obj;
lean_object* v___y_522_ = stack[9].m_obj;
lean_object* v_res_633_;
v_res_633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_as_513_, v_sz_514_, v_i_515_, v_b_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6___boxed(lean_object* v_as_634_, lean_object* v_sz_635_, lean_object* v_i_636_, lean_object* v_b_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
size_t v_sz_boxed_645_; size_t v_i_boxed_646_; lean_object* v_res_647_; 
v_sz_boxed_645_ = lean_unbox_usize(v_sz_635_);
lean_dec(v_sz_635_);
v_i_boxed_646_ = lean_unbox_usize(v_i_636_);
lean_dec(v_i_636_);
v_res_647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_as_634_, v_sz_boxed_645_, v_i_boxed_646_, v_b_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v_as_634_);
return v_res_647_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(lean_object* v_init_648_, lean_object* v_n_649_, lean_object* v_b_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
if (lean_obj_tag(v_n_649_) == 0)
{
lean_object* v_cs_658_; lean_object* v___x_659_; lean_object* v___x_660_; size_t v_sz_661_; size_t v___x_662_; lean_object* v___x_663_; 
v_cs_658_ = lean_ctor_get(v_n_649_, 0);
v___x_659_ = lean_box(0);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v_b_650_);
v_sz_661_ = lean_array_size(v_cs_658_);
v___x_662_ = ((size_t)0ULL);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_648_, v_cs_658_, v_sz_661_, v___x_662_, v___x_660_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_678_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_678_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_678_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_678_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_fst_668_; 
v_fst_668_ = lean_ctor_get(v_a_664_, 0);
if (lean_obj_tag(v_fst_668_) == 0)
{
lean_object* v_snd_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v_snd_669_ = lean_ctor_get(v_a_664_, 1);
lean_inc(v_snd_669_);
lean_dec(v_a_664_);
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v_snd_669_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_670_);
v___x_672_ = v___x_666_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
else
{
lean_object* v_val_674_; lean_object* v___x_676_; 
lean_inc_ref(v_fst_668_);
lean_dec(v_a_664_);
v_val_674_ = lean_ctor_get(v_fst_668_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v_fst_668_, 1);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v_val_674_);
v___x_676_ = v___x_666_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_val_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
v_a_679_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_663_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_663_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v_vs_687_; lean_object* v___x_688_; lean_object* v___x_689_; size_t v_sz_690_; size_t v___x_691_; lean_object* v___x_692_; 
v_vs_687_ = lean_ctor_get(v_n_649_, 0);
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v_b_650_);
v_sz_690_ = lean_array_size(v_vs_687_);
v___x_691_ = ((size_t)0ULL);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_vs_687_, v_sz_690_, v___x_691_, v___x_689_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_707_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_707_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_707_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_707_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_fst_697_; 
v_fst_697_ = lean_ctor_get(v_a_693_, 0);
if (lean_obj_tag(v_fst_697_) == 0)
{
lean_object* v_snd_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v_snd_698_ = lean_ctor_get(v_a_693_, 1);
lean_inc(v_snd_698_);
lean_dec(v_a_693_);
v___x_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_699_, 0, v_snd_698_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_699_);
v___x_701_ = v___x_695_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
else
{
lean_object* v_val_703_; lean_object* v___x_705_; 
lean_inc_ref(v_fst_697_);
lean_dec(v_a_693_);
v_val_703_ = lean_ctor_get(v_fst_697_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v_fst_697_, 1);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v_val_703_);
v___x_705_ = v___x_695_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_val_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
v_a_708_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_692_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_692_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_648_ = stack[0].m_obj;
lean_object* v_n_649_ = stack[1].m_obj;
lean_object* v_b_650_ = stack[2].m_obj;
lean_object* v___y_651_ = stack[3].m_obj;
lean_object* v___y_652_ = stack[4].m_obj;
lean_object* v___y_653_ = stack[5].m_obj;
lean_object* v___y_654_ = stack[6].m_obj;
lean_object* v___y_655_ = stack[7].m_obj;
lean_object* v___y_656_ = stack[8].m_obj;
lean_object* v_res_716_;
v_res_716_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_648_, v_n_649_, v_b_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
stack->m_obj
 = v_res_716_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(lean_object* v_init_717_, lean_object* v_as_718_, size_t v_sz_719_, size_t v_i_720_, lean_object* v_b_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = lean_usize_dec_lt(v_i_720_, v_sz_719_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v_b_721_);
return v___x_730_;
}
else
{
lean_object* v_snd_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_765_; 
v_snd_731_ = lean_ctor_get(v_b_721_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_b_721_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v_b_721_, 0);
lean_dec(v_unused_766_);
v___x_733_ = v_b_721_;
v_isShared_734_ = v_isSharedCheck_765_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_snd_731_);
lean_dec(v_b_721_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_765_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v_a_736_; lean_object* v___x_737_; 
v___x_735_ = lean_box(0);
v_a_736_ = lean_array_uget_borrowed(v_as_718_, v_i_720_);
lean_inc(v_snd_731_);
v___x_737_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_717_, v_a_736_, v_snd_731_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_756_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_756_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_756_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_756_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
if (lean_obj_tag(v_a_738_) == 0)
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v_a_738_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_742_);
v___x_744_ = v___x_733_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_snd_731_);
v___x_744_ = v_reuseFailAlloc_748_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_744_);
v___x_746_ = v___x_740_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; 
lean_del_object(v___x_740_);
lean_dec(v_snd_731_);
v_a_749_ = lean_ctor_get(v_a_738_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v_a_738_, 1);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v_a_749_);
lean_ctor_set(v___x_733_, 0, v___x_735_);
v___x_751_ = v___x_733_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_a_749_);
v___x_751_ = v_reuseFailAlloc_755_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
size_t v___x_752_; size_t v___x_753_; 
v___x_752_ = ((size_t)1ULL);
v___x_753_ = lean_usize_add(v_i_720_, v___x_752_);
v_i_720_ = v___x_753_;
v_b_721_ = v___x_751_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_del_object(v___x_733_);
lean_dec(v_snd_731_);
v_a_757_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_737_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_737_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
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
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_717_ = stack[0].m_obj;
lean_object* v_as_718_ = stack[1].m_obj;
size_t v_sz_719_ = stack[2].m_num;
size_t v_i_720_ = stack[3].m_num;
lean_object* v_b_721_ = stack[4].m_obj;
lean_object* v___y_722_ = stack[5].m_obj;
lean_object* v___y_723_ = stack[6].m_obj;
lean_object* v___y_724_ = stack[7].m_obj;
lean_object* v___y_725_ = stack[8].m_obj;
lean_object* v___y_726_ = stack[9].m_obj;
lean_object* v___y_727_ = stack[10].m_obj;
lean_object* v_res_767_;
v_res_767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_717_, v_as_718_, v_sz_719_, v_i_720_, v_b_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
stack->m_obj
 = v_res_767_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_init_768_, lean_object* v_as_769_, lean_object* v_sz_770_, lean_object* v_i_771_, lean_object* v_b_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
size_t v_sz_boxed_780_; size_t v_i_boxed_781_; lean_object* v_res_782_; 
v_sz_boxed_780_ = lean_unbox_usize(v_sz_770_);
lean_dec(v_sz_770_);
v_i_boxed_781_ = lean_unbox_usize(v_i_771_);
lean_dec(v_i_771_);
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_768_, v_as_769_, v_sz_boxed_780_, v_i_boxed_781_, v_b_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec_ref(v_as_769_);
lean_dec_ref(v_init_768_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2___boxed(lean_object* v_init_783_, lean_object* v_n_784_, lean_object* v_b_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_783_, v_n_784_, v_b_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec_ref(v_n_784_);
lean_dec_ref(v_init_783_);
return v_res_793_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(lean_object* v_as_794_, size_t v_sz_795_, size_t v_i_796_, lean_object* v_b_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
uint8_t v___x_805_; 
v___x_805_ = lean_usize_dec_lt(v_i_796_, v_sz_795_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v_b_797_);
return v___x_806_;
}
else
{
lean_object* v_snd_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_912_; 
v_snd_807_ = lean_ctor_get(v_b_797_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v_b_797_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v_b_797_, 0);
lean_dec(v_unused_913_);
v___x_809_ = v_b_797_;
v_isShared_810_ = v_isSharedCheck_912_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_snd_807_);
lean_dec(v_b_797_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_912_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v_a_813_; lean_object* v_a_820_; 
v___x_811_ = lean_box(0);
v_a_820_ = lean_array_uget(v_as_794_, v_i_796_);
if (lean_obj_tag(v_a_820_) == 0)
{
v_a_813_ = v_snd_807_;
goto v___jp_812_;
}
else
{
lean_object* v_snd_821_; lean_object* v_val_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_911_; 
v_snd_821_ = lean_ctor_get(v_snd_807_, 1);
lean_inc(v_snd_821_);
v_val_822_ = lean_ctor_get(v_a_820_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v_a_820_);
if (v_isSharedCheck_911_ == 0)
{
v___x_824_ = v_a_820_;
v_isShared_825_ = v_isSharedCheck_911_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_val_822_);
lean_dec(v_a_820_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_911_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_fst_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_909_; 
v_fst_826_ = lean_ctor_get(v_snd_807_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v_snd_807_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; 
v_unused_910_ = lean_ctor_get(v_snd_807_, 1);
lean_dec(v_unused_910_);
v___x_828_ = v_snd_807_;
v_isShared_829_ = v_isSharedCheck_909_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_fst_826_);
lean_dec(v_snd_807_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_909_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_fst_830_; lean_object* v_snd_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_908_; 
v_fst_830_ = lean_ctor_get(v_snd_821_, 0);
v_snd_831_ = lean_ctor_get(v_snd_821_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_snd_821_);
if (v_isSharedCheck_908_ == 0)
{
v___x_833_ = v_snd_821_;
v_isShared_834_ = v_isSharedCheck_908_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_snd_831_);
lean_inc(v_fst_830_);
lean_dec(v_snd_821_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_908_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_decl_836_; 
if (lean_obj_tag(v_val_822_) == 0)
{
lean_object* v_fvarId_851_; lean_object* v_userName_852_; lean_object* v_type_853_; uint8_t v_bi_854_; uint8_t v_kind_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_872_; 
v_fvarId_851_ = lean_ctor_get(v_val_822_, 1);
v_userName_852_ = lean_ctor_get(v_val_822_, 2);
v_type_853_ = lean_ctor_get(v_val_822_, 3);
v_bi_854_ = lean_ctor_get_uint8(v_val_822_, sizeof(void*)*4);
v_kind_855_ = lean_ctor_get_uint8(v_val_822_, sizeof(void*)*4 + 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v_val_822_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v_val_822_, 0);
lean_dec(v_unused_873_);
v___x_857_ = v_val_822_;
v_isShared_858_ = v_isSharedCheck_872_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_type_853_);
lean_inc(v_userName_852_);
lean_inc(v_fvarId_851_);
lean_dec(v_val_822_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_872_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Meta_Sym_preprocessExpr(v_type_853_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
lean_inc(v_snd_831_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 3, v_a_860_);
lean_ctor_set(v___x_857_, 0, v_snd_831_);
v___x_862_ = v___x_857_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_snd_831_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_fvarId_851_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_userName_852_);
lean_ctor_set(v_reuseFailAlloc_863_, 3, v_a_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_863_, sizeof(void*)*4, v_bi_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_863_, sizeof(void*)*4 + 1, v_kind_855_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
v_decl_836_ = v___x_862_;
goto v___jp_835_;
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_del_object(v___x_857_);
lean_dec(v_userName_852_);
lean_dec(v_fvarId_851_);
lean_del_object(v___x_833_);
lean_dec(v_snd_831_);
lean_dec(v_fst_830_);
lean_del_object(v___x_828_);
lean_dec(v_fst_826_);
lean_del_object(v___x_824_);
lean_del_object(v___x_809_);
v_a_864_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_859_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_859_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
else
{
lean_object* v_fvarId_874_; lean_object* v_userName_875_; lean_object* v_type_876_; lean_object* v_value_877_; uint8_t v_nondep_878_; uint8_t v_kind_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_906_; 
v_fvarId_874_ = lean_ctor_get(v_val_822_, 1);
v_userName_875_ = lean_ctor_get(v_val_822_, 2);
v_type_876_ = lean_ctor_get(v_val_822_, 3);
v_value_877_ = lean_ctor_get(v_val_822_, 4);
v_nondep_878_ = lean_ctor_get_uint8(v_val_822_, sizeof(void*)*5);
v_kind_879_ = lean_ctor_get_uint8(v_val_822_, sizeof(void*)*5 + 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_val_822_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; 
v_unused_907_ = lean_ctor_get(v_val_822_, 0);
lean_dec(v_unused_907_);
v___x_881_ = v_val_822_;
v_isShared_882_ = v_isSharedCheck_906_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_value_877_);
lean_inc(v_type_876_);
lean_inc(v_userName_875_);
lean_inc(v_fvarId_874_);
lean_dec(v_val_822_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_906_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Meta_Sym_preprocessExpr(v_type_876_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = l_Lean_Meta_Sym_preprocessExpr(v_value_877_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
lean_inc(v_snd_831_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 4, v_a_886_);
lean_ctor_set(v___x_881_, 3, v_a_884_);
lean_ctor_set(v___x_881_, 0, v_snd_831_);
v___x_888_ = v___x_881_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_snd_831_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_fvarId_874_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_userName_875_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_a_884_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_a_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_889_, sizeof(void*)*5, v_nondep_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_889_, sizeof(void*)*5 + 1, v_kind_879_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
v_decl_836_ = v___x_888_;
goto v___jp_835_;
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec(v_a_884_);
lean_del_object(v___x_881_);
lean_dec(v_userName_875_);
lean_dec(v_fvarId_874_);
lean_del_object(v___x_833_);
lean_dec(v_snd_831_);
lean_dec(v_fst_830_);
lean_del_object(v___x_828_);
lean_dec(v_fst_826_);
lean_del_object(v___x_824_);
lean_del_object(v___x_809_);
v_a_890_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_885_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_885_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_del_object(v___x_881_);
lean_dec_ref(v_value_877_);
lean_dec(v_userName_875_);
lean_dec(v_fvarId_874_);
lean_del_object(v___x_833_);
lean_dec(v_snd_831_);
lean_dec(v_fst_830_);
lean_del_object(v___x_828_);
lean_dec(v_fst_826_);
lean_del_object(v___x_824_);
lean_del_object(v___x_809_);
v_a_898_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_883_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_883_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
v___jp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_nat_add(v_snd_831_, v___x_837_);
lean_dec(v_snd_831_);
lean_inc_ref(v_decl_836_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_decl_836_);
v___x_840_ = v___x_824_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_decl_836_);
v___x_840_ = v_reuseFailAlloc_850_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_841_ = l_Lean_PersistentArray_push___redArg(v_fst_830_, v___x_840_);
v___x_842_ = l_Lean_LocalDecl_fvarId(v_decl_836_);
v___x_843_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_826_, v___x_842_, v_decl_836_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v___x_838_);
lean_ctor_set(v___x_833_, 0, v___x_841_);
v___x_845_ = v___x_833_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v___x_838_);
v___x_845_ = v_reuseFailAlloc_849_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_845_);
lean_ctor_set(v___x_828_, 0, v___x_843_);
v___x_847_ = v___x_828_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
v_a_813_ = v___x_847_;
goto v___jp_812_;
}
}
}
}
}
}
}
}
v___jp_812_:
{
lean_object* v___x_815_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 1, v_a_813_);
lean_ctor_set(v___x_809_, 0, v___x_811_);
v___x_815_ = v___x_809_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_a_813_);
v___x_815_ = v_reuseFailAlloc_819_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
size_t v___x_816_; size_t v___x_817_; 
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_add(v_i_796_, v___x_816_);
v_i_796_ = v___x_817_;
v_b_797_ = v___x_815_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_794_ = stack[0].m_obj;
size_t v_sz_795_ = stack[1].m_num;
size_t v_i_796_ = stack[2].m_num;
lean_object* v_b_797_ = stack[3].m_obj;
lean_object* v___y_798_ = stack[4].m_obj;
lean_object* v___y_799_ = stack[5].m_obj;
lean_object* v___y_800_ = stack[6].m_obj;
lean_object* v___y_801_ = stack[7].m_obj;
lean_object* v___y_802_ = stack[8].m_obj;
lean_object* v___y_803_ = stack[9].m_obj;
lean_object* v_res_914_;
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_794_, v_sz_795_, v_i_796_, v_b_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
stack->m_obj
 = v_res_914_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8___boxed(lean_object* v_as_915_, lean_object* v_sz_916_, lean_object* v_i_917_, lean_object* v_b_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
size_t v_sz_boxed_926_; size_t v_i_boxed_927_; lean_object* v_res_928_; 
v_sz_boxed_926_ = lean_unbox_usize(v_sz_916_);
lean_dec(v_sz_916_);
v_i_boxed_927_ = lean_unbox_usize(v_i_917_);
lean_dec(v_i_917_);
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_915_, v_sz_boxed_926_, v_i_boxed_927_, v_b_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec_ref(v_as_915_);
return v_res_928_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(lean_object* v_as_929_, size_t v_sz_930_, size_t v_i_931_, lean_object* v_b_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
uint8_t v___x_940_; 
v___x_940_ = lean_usize_dec_lt(v_i_931_, v_sz_930_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v_b_932_);
return v___x_941_;
}
else
{
lean_object* v_snd_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_1047_; 
v_snd_942_ = lean_ctor_get(v_b_932_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_b_932_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; 
v_unused_1048_ = lean_ctor_get(v_b_932_, 0);
lean_dec(v_unused_1048_);
v___x_944_ = v_b_932_;
v_isShared_945_ = v_isSharedCheck_1047_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_snd_942_);
lean_dec(v_b_932_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_1047_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v_a_948_; lean_object* v_a_955_; 
v___x_946_ = lean_box(0);
v_a_955_ = lean_array_uget(v_as_929_, v_i_931_);
if (lean_obj_tag(v_a_955_) == 0)
{
v_a_948_ = v_snd_942_;
goto v___jp_947_;
}
else
{
lean_object* v_snd_956_; lean_object* v_val_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_1046_; 
v_snd_956_ = lean_ctor_get(v_snd_942_, 1);
lean_inc(v_snd_956_);
v_val_957_ = lean_ctor_get(v_a_955_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_a_955_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_959_ = v_a_955_;
v_isShared_960_ = v_isSharedCheck_1046_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_val_957_);
lean_dec(v_a_955_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_1046_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_fst_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1044_; 
v_fst_961_ = lean_ctor_get(v_snd_942_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_snd_942_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v_snd_942_, 1);
lean_dec(v_unused_1045_);
v___x_963_ = v_snd_942_;
v_isShared_964_ = v_isSharedCheck_1044_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_fst_961_);
lean_dec(v_snd_942_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1044_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v_fst_965_; lean_object* v_snd_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_1043_; 
v_fst_965_ = lean_ctor_get(v_snd_956_, 0);
v_snd_966_ = lean_ctor_get(v_snd_956_, 1);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_snd_956_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_968_ = v_snd_956_;
v_isShared_969_ = v_isSharedCheck_1043_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_snd_966_);
lean_inc(v_fst_965_);
lean_dec(v_snd_956_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_1043_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v_decl_971_; 
if (lean_obj_tag(v_val_957_) == 0)
{
lean_object* v_fvarId_986_; lean_object* v_userName_987_; lean_object* v_type_988_; uint8_t v_bi_989_; uint8_t v_kind_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1007_; 
v_fvarId_986_ = lean_ctor_get(v_val_957_, 1);
v_userName_987_ = lean_ctor_get(v_val_957_, 2);
v_type_988_ = lean_ctor_get(v_val_957_, 3);
v_bi_989_ = lean_ctor_get_uint8(v_val_957_, sizeof(void*)*4);
v_kind_990_ = lean_ctor_get_uint8(v_val_957_, sizeof(void*)*4 + 1);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_val_957_);
if (v_isSharedCheck_1007_ == 0)
{
lean_object* v_unused_1008_; 
v_unused_1008_ = lean_ctor_get(v_val_957_, 0);
lean_dec(v_unused_1008_);
v___x_992_ = v_val_957_;
v_isShared_993_ = v_isSharedCheck_1007_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_type_988_);
lean_inc(v_userName_987_);
lean_inc(v_fvarId_986_);
lean_dec(v_val_957_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1007_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_Meta_Sym_preprocessExpr(v_type_988_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
lean_inc(v_snd_966_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 3, v_a_995_);
lean_ctor_set(v___x_992_, 0, v_snd_966_);
v___x_997_ = v___x_992_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_snd_966_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_fvarId_986_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_userName_987_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_a_995_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, sizeof(void*)*4, v_bi_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, sizeof(void*)*4 + 1, v_kind_990_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
v_decl_971_ = v___x_997_;
goto v___jp_970_;
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_del_object(v___x_992_);
lean_dec(v_userName_987_);
lean_dec(v_fvarId_986_);
lean_del_object(v___x_968_);
lean_dec(v_snd_966_);
lean_dec(v_fst_965_);
lean_del_object(v___x_963_);
lean_dec(v_fst_961_);
lean_del_object(v___x_959_);
lean_del_object(v___x_944_);
v_a_999_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_994_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_994_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
else
{
lean_object* v_fvarId_1009_; lean_object* v_userName_1010_; lean_object* v_type_1011_; lean_object* v_value_1012_; uint8_t v_nondep_1013_; uint8_t v_kind_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1041_; 
v_fvarId_1009_ = lean_ctor_get(v_val_957_, 1);
v_userName_1010_ = lean_ctor_get(v_val_957_, 2);
v_type_1011_ = lean_ctor_get(v_val_957_, 3);
v_value_1012_ = lean_ctor_get(v_val_957_, 4);
v_nondep_1013_ = lean_ctor_get_uint8(v_val_957_, sizeof(void*)*5);
v_kind_1014_ = lean_ctor_get_uint8(v_val_957_, sizeof(void*)*5 + 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_val_957_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; 
v_unused_1042_ = lean_ctor_get(v_val_957_, 0);
lean_dec(v_unused_1042_);
v___x_1016_ = v_val_957_;
v_isShared_1017_ = v_isSharedCheck_1041_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_value_1012_);
lean_inc(v_type_1011_);
lean_inc(v_userName_1010_);
lean_inc(v_fvarId_1009_);
lean_dec(v_val_957_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1041_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_Meta_Sym_preprocessExpr(v_type_1011_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = l_Lean_Meta_Sym_preprocessExpr(v_value_1012_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
lean_inc(v_snd_966_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 4, v_a_1021_);
lean_ctor_set(v___x_1016_, 3, v_a_1019_);
lean_ctor_set(v___x_1016_, 0, v_snd_966_);
v___x_1023_ = v___x_1016_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_snd_966_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_fvarId_1009_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v_userName_1010_);
lean_ctor_set(v_reuseFailAlloc_1024_, 3, v_a_1019_);
lean_ctor_set(v_reuseFailAlloc_1024_, 4, v_a_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1024_, sizeof(void*)*5, v_nondep_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1024_, sizeof(void*)*5 + 1, v_kind_1014_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
v_decl_971_ = v___x_1023_;
goto v___jp_970_;
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v_a_1019_);
lean_del_object(v___x_1016_);
lean_dec(v_userName_1010_);
lean_dec(v_fvarId_1009_);
lean_del_object(v___x_968_);
lean_dec(v_snd_966_);
lean_dec(v_fst_965_);
lean_del_object(v___x_963_);
lean_dec(v_fst_961_);
lean_del_object(v___x_959_);
lean_del_object(v___x_944_);
v_a_1025_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1020_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1020_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_del_object(v___x_1016_);
lean_dec_ref(v_value_1012_);
lean_dec(v_userName_1010_);
lean_dec(v_fvarId_1009_);
lean_del_object(v___x_968_);
lean_dec(v_snd_966_);
lean_dec(v_fst_965_);
lean_del_object(v___x_963_);
lean_dec(v_fst_961_);
lean_del_object(v___x_959_);
lean_del_object(v___x_944_);
v_a_1033_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1018_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1018_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
v___jp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_972_ = lean_unsigned_to_nat(1u);
v___x_973_ = lean_nat_add(v_snd_966_, v___x_972_);
lean_dec(v_snd_966_);
lean_inc_ref(v_decl_971_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v_decl_971_);
v___x_975_ = v___x_959_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_decl_971_);
v___x_975_ = v_reuseFailAlloc_985_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_976_ = l_Lean_PersistentArray_push___redArg(v_fst_965_, v___x_975_);
v___x_977_ = l_Lean_LocalDecl_fvarId(v_decl_971_);
v___x_978_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_961_, v___x_977_, v_decl_971_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v___x_973_);
lean_ctor_set(v___x_968_, 0, v___x_976_);
v___x_980_ = v___x_968_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_973_);
v___x_980_ = v_reuseFailAlloc_984_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_982_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v___x_980_);
lean_ctor_set(v___x_963_, 0, v___x_978_);
v___x_982_ = v___x_963_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
v_a_948_ = v___x_982_;
goto v___jp_947_;
}
}
}
}
}
}
}
}
v___jp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v_a_948_);
lean_ctor_set(v___x_944_, 0, v___x_946_);
v___x_950_ = v___x_944_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_a_948_);
v___x_950_ = v_reuseFailAlloc_954_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
size_t v___x_951_; size_t v___x_952_; lean_object* v___x_953_; 
v___x_951_ = ((size_t)1ULL);
v___x_952_ = lean_usize_add(v_i_931_, v___x_951_);
v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_929_, v_sz_930_, v___x_952_, v___x_950_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
return v___x_953_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_929_ = stack[0].m_obj;
size_t v_sz_930_ = stack[1].m_num;
size_t v_i_931_ = stack[2].m_num;
lean_object* v_b_932_ = stack[3].m_obj;
lean_object* v___y_933_ = stack[4].m_obj;
lean_object* v___y_934_ = stack[5].m_obj;
lean_object* v___y_935_ = stack[6].m_obj;
lean_object* v___y_936_ = stack[7].m_obj;
lean_object* v___y_937_ = stack[8].m_obj;
lean_object* v___y_938_ = stack[9].m_obj;
lean_object* v_res_1049_;
v_res_1049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_as_929_, v_sz_930_, v_i_931_, v_b_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
stack->m_obj
 = v_res_1049_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3___boxed(lean_object* v_as_1050_, lean_object* v_sz_1051_, lean_object* v_i_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
size_t v_sz_boxed_1061_; size_t v_i_boxed_1062_; lean_object* v_res_1063_; 
v_sz_boxed_1061_ = lean_unbox_usize(v_sz_1051_);
lean_dec(v_sz_1051_);
v_i_boxed_1062_ = lean_unbox_usize(v_i_1052_);
lean_dec(v_i_1052_);
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_as_1050_, v_sz_boxed_1061_, v_i_boxed_1062_, v_b_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec_ref(v_as_1050_);
return v_res_1063_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(lean_object* v_t_1064_, lean_object* v_init_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_root_1073_; lean_object* v_tail_1074_; lean_object* v___x_1075_; 
v_root_1073_ = lean_ctor_get(v_t_1064_, 0);
v_tail_1074_ = lean_ctor_get(v_t_1064_, 1);
lean_inc_ref(v_init_1065_);
v___x_1075_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_1065_, v_root_1073_, v_init_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec_ref(v_init_1065_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1112_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1112_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1112_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
if (lean_obj_tag(v_a_1076_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; 
v_a_1080_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v_a_1076_, 1);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v_a_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; size_t v_sz_1087_; size_t v___x_1088_; lean_object* v___x_1089_; 
lean_del_object(v___x_1078_);
v_a_1084_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v_a_1076_, 1);
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v_a_1084_);
v_sz_1087_ = lean_array_size(v_tail_1074_);
v___x_1088_ = ((size_t)0ULL);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_tail_1074_, v_sz_1087_, v___x_1088_, v___x_1086_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1103_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1103_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1103_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_fst_1094_; 
v_fst_1094_ = lean_ctor_get(v_a_1090_, 0);
if (lean_obj_tag(v_fst_1094_) == 0)
{
lean_object* v_snd_1095_; lean_object* v___x_1097_; 
v_snd_1095_ = lean_ctor_get(v_a_1090_, 1);
lean_inc(v_snd_1095_);
lean_dec(v_a_1090_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v_snd_1095_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_snd_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
else
{
lean_object* v_val_1099_; lean_object* v___x_1101_; 
lean_inc_ref(v_fst_1094_);
lean_dec(v_a_1090_);
v_val_1099_ = lean_ctor_get(v_fst_1094_, 0);
lean_inc(v_val_1099_);
lean_dec_ref_known(v_fst_1094_, 1);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v_val_1099_);
v___x_1101_ = v___x_1092_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_val_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1089_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1089_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
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
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
v_a_1113_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1075_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1075_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1064_ = stack[0].m_obj;
lean_object* v_init_1065_ = stack[1].m_obj;
lean_object* v___y_1066_ = stack[2].m_obj;
lean_object* v___y_1067_ = stack[3].m_obj;
lean_object* v___y_1068_ = stack[4].m_obj;
lean_object* v___y_1069_ = stack[5].m_obj;
lean_object* v___y_1070_ = stack[6].m_obj;
lean_object* v___y_1071_ = stack[7].m_obj;
lean_object* v_res_1121_;
v_res_1121_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_t_1064_, v_init_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
stack->m_obj
 = v_res_1121_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1___boxed(lean_object* v_t_1122_, lean_object* v_init_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_t_1122_, v_init_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec_ref(v_t_1122_);
return v_res_1131_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0(void){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1132_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1(void){
_start:
{
lean_object* v___x_1133_; lean_object* v_fvarIdToDecl_1134_; 
v___x_1133_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0);
v_fvarIdToDecl_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fvarIdToDecl_1134_, 0, v___x_1133_);
return v_fvarIdToDecl_1134_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = lean_unsigned_to_nat(32u);
v___x_1136_ = lean_mk_empty_array_with_capacity(v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3(void){
_start:
{
size_t v___x_1138_; lean_object* v_index_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v_decls_1143_; 
v___x_1138_ = ((size_t)5ULL);
v_index_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = lean_unsigned_to_nat(32u);
v___x_1141_ = lean_mk_empty_array_with_capacity(v___x_1140_);
v___x_1142_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2);
v_decls_1143_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_decls_1143_, 0, v___x_1142_);
lean_ctor_set(v_decls_1143_, 1, v___x_1141_);
lean_ctor_set(v_decls_1143_, 2, v_index_1139_);
lean_ctor_set(v_decls_1143_, 3, v_index_1139_);
lean_ctor_set_usize(v_decls_1143_, 4, v___x_1138_);
return v_decls_1143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4(void){
_start:
{
lean_object* v_index_1144_; lean_object* v_decls_1145_; lean_object* v___x_1146_; 
v_index_1144_ = lean_unsigned_to_nat(0u);
v_decls_1145_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3);
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_decls_1145_);
lean_ctor_set(v___x_1146_, 1, v_index_1144_);
return v___x_1146_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5(void){
_start:
{
lean_object* v___x_1147_; lean_object* v_fvarIdToDecl_1148_; lean_object* v___x_1149_; 
v___x_1147_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4);
v_fvarIdToDecl_1148_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1);
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v_fvarIdToDecl_1148_);
lean_ctor_set(v___x_1149_, 1, v___x_1147_);
return v___x_1149_;
}
}
lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(lean_object* v_lctx_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_decls_1158_; lean_object* v_auxDeclToFullName_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1187_; 
v_decls_1158_ = lean_ctor_get(v_lctx_1150_, 1);
v_auxDeclToFullName_1159_ = lean_ctor_get(v_lctx_1150_, 2);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_lctx_1150_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v_lctx_1150_, 0);
lean_dec(v_unused_1188_);
v___x_1161_ = v_lctx_1150_;
v_isShared_1162_ = v_isSharedCheck_1187_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_auxDeclToFullName_1159_);
lean_inc(v_decls_1158_);
lean_dec(v_lctx_1150_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1187_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5);
v___x_1164_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_decls_1158_, v___x_1163_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec_ref(v_decls_1158_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1178_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1178_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1178_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_snd_1169_; lean_object* v_fst_1170_; lean_object* v_fst_1171_; lean_object* v___x_1173_; 
v_snd_1169_ = lean_ctor_get(v_a_1165_, 1);
lean_inc(v_snd_1169_);
v_fst_1170_ = lean_ctor_get(v_a_1165_, 0);
lean_inc(v_fst_1170_);
lean_dec(v_a_1165_);
v_fst_1171_ = lean_ctor_get(v_snd_1169_, 0);
lean_inc(v_fst_1171_);
lean_dec(v_snd_1169_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v_fst_1171_);
lean_ctor_set(v___x_1161_, 0, v_fst_1170_);
v___x_1173_ = v___x_1161_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_fst_1170_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_fst_1171_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_auxDeclToFullName_1159_);
v___x_1173_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1175_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1173_);
v___x_1175_ = v___x_1167_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_del_object(v___x_1161_);
lean_dec(v_auxDeclToFullName_1159_);
v_a_1179_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1164_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1164_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1150_ = stack[0].m_obj;
lean_object* v_a_1151_ = stack[1].m_obj;
lean_object* v_a_1152_ = stack[2].m_obj;
lean_object* v_a_1153_ = stack[3].m_obj;
lean_object* v_a_1154_ = stack[4].m_obj;
lean_object* v_a_1155_ = stack[5].m_obj;
lean_object* v_a_1156_ = stack[6].m_obj;
lean_object* v_res_1189_;
v_res_1189_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
stack->m_obj
 = v_res_1189_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___boxed(lean_object* v_lctx_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0(lean_object* v_00_u03b2_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_x_1200_, v_x_1201_, v_x_1202_);
return v___x_1203_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(lean_object* v_00_u03b2_1204_, lean_object* v_x_1205_, size_t v_x_1206_, size_t v_x_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_1205_, v_x_1206_, v_x_1207_, v_x_1208_, v_x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1205_ = stack[1].m_obj;
size_t v_x_1206_ = stack[2].m_num;
size_t v_x_1207_ = stack[3].m_num;
lean_object* v_x_1208_ = stack[4].m_obj;
lean_object* v_x_1209_ = stack[5].m_obj;
lean_object* v_res_1211_;
v_res_1211_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(lean_box(0), v_x_1205_, v_x_1206_, v_x_1207_, v_x_1208_, v_x_1209_);
stack->m_obj
 = v_res_1211_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1212_, lean_object* v_x_1213_, lean_object* v_x_1214_, lean_object* v_x_1215_, lean_object* v_x_1216_, lean_object* v_x_1217_){
_start:
{
size_t v_x_11505__boxed_1218_; size_t v_x_11506__boxed_1219_; lean_object* v_res_1220_; 
v_x_11505__boxed_1218_ = lean_unbox_usize(v_x_1214_);
lean_dec(v_x_1214_);
v_x_11506__boxed_1219_ = lean_unbox_usize(v_x_1215_);
lean_dec(v_x_1215_);
v_res_1220_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(v_00_u03b2_1212_, v_x_1213_, v_x_11505__boxed_1218_, v_x_11506__boxed_1219_, v_x_1216_, v_x_1217_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1221_, lean_object* v_n_1222_, lean_object* v_k_1223_, lean_object* v_v_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v_n_1222_, v_k_1223_, v_v_1224_);
return v___x_1225_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1226_, size_t v_depth_1227_, lean_object* v_keys_1228_, lean_object* v_vals_1229_, lean_object* v_heq_1230_, lean_object* v_i_1231_, lean_object* v_entries_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_1227_, v_keys_1228_, v_vals_1229_, v_i_1231_, v_entries_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1227_ = stack[1].m_num;
lean_object* v_keys_1228_ = stack[2].m_obj;
lean_object* v_vals_1229_ = stack[3].m_obj;
lean_object* v_i_1231_ = stack[5].m_obj;
lean_object* v_entries_1232_ = stack[6].m_obj;
lean_object* v_res_1234_;
v_res_1234_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(lean_box(0), v_depth_1227_, v_keys_1228_, v_vals_1229_, lean_box(0), v_i_1231_, v_entries_1232_);
stack->m_obj
 = v_res_1234_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1235_, lean_object* v_depth_1236_, lean_object* v_keys_1237_, lean_object* v_vals_1238_, lean_object* v_heq_1239_, lean_object* v_i_1240_, lean_object* v_entries_1241_){
_start:
{
size_t v_depth_boxed_1242_; lean_object* v_res_1243_; 
v_depth_boxed_1242_ = lean_unbox_usize(v_depth_1236_);
lean_dec(v_depth_1236_);
v_res_1243_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(v_00_u03b2_1235_, v_depth_boxed_1242_, v_keys_1237_, v_vals_1238_, v_heq_1239_, v_i_1240_, v_entries_1241_);
lean_dec_ref(v_vals_1238_);
lean_dec_ref(v_keys_1237_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1245_, v_x_1246_, v_x_1247_, v_x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
lean_object* v_ks_1254_; lean_object* v_vs_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1279_; 
v_ks_1254_ = lean_ctor_get(v_x_1250_, 0);
v_vs_1255_ = lean_ctor_get(v_x_1250_, 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_x_1250_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1257_ = v_x_1250_;
v_isShared_1258_ = v_isSharedCheck_1279_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_vs_1255_);
lean_inc(v_ks_1254_);
lean_dec(v_x_1250_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1279_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = lean_array_get_size(v_ks_1254_);
v___x_1260_ = lean_nat_dec_lt(v_x_1251_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
lean_dec(v_x_1251_);
v___x_1261_ = lean_array_push(v_ks_1254_, v_x_1252_);
v___x_1262_ = lean_array_push(v_vs_1255_, v_x_1253_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v___x_1262_);
lean_ctor_set(v___x_1257_, 0, v___x_1261_);
v___x_1264_ = v___x_1257_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
else
{
lean_object* v_k_x27_1266_; uint8_t v___x_1267_; 
v_k_x27_1266_ = lean_array_fget_borrowed(v_ks_1254_, v_x_1251_);
v___x_1267_ = l_Lean_instBEqMVarId_beq(v_x_1252_, v_k_x27_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1269_; 
if (v_isShared_1258_ == 0)
{
v___x_1269_ = v___x_1257_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_ks_1254_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_vs_1255_);
v___x_1269_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = lean_unsigned_to_nat(1u);
v___x_1271_ = lean_nat_add(v_x_1251_, v___x_1270_);
lean_dec(v_x_1251_);
v_x_1250_ = v___x_1269_;
v_x_1251_ = v___x_1271_;
goto _start;
}
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1274_ = lean_array_fset(v_ks_1254_, v_x_1251_, v_x_1252_);
v___x_1275_ = lean_array_fset(v_vs_1255_, v_x_1251_, v_x_1253_);
lean_dec(v_x_1251_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v___x_1275_);
lean_ctor_set(v___x_1257_, 0, v___x_1274_);
v___x_1277_ = v___x_1257_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1280_, lean_object* v_k_1281_, lean_object* v_v_1282_){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1280_, v___x_1283_, v_k_1281_, v_v_1282_);
return v___x_1284_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1285_, size_t v_x_1286_, size_t v_x_1287_, lean_object* v_x_1288_, lean_object* v_x_1289_){
_start:
{
if (lean_obj_tag(v_x_1285_) == 0)
{
lean_object* v_es_1290_; size_t v___x_1291_; size_t v___x_1292_; lean_object* v_j_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v_es_1290_ = lean_ctor_get(v_x_1285_, 0);
v___x_1291_ = ((size_t)31ULL);
v___x_1292_ = lean_usize_land(v_x_1286_, v___x_1291_);
v_j_1293_ = lean_usize_to_nat(v___x_1292_);
v___x_1294_ = lean_array_get_size(v_es_1290_);
v___x_1295_ = lean_nat_dec_lt(v_j_1293_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_dec(v_j_1293_);
lean_dec(v_x_1289_);
lean_dec(v_x_1288_);
return v_x_1285_;
}
else
{
lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1334_; 
lean_inc_ref(v_es_1290_);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_x_1285_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; 
v_unused_1335_ = lean_ctor_get(v_x_1285_, 0);
lean_dec(v_unused_1335_);
v___x_1297_ = v_x_1285_;
v_isShared_1298_ = v_isSharedCheck_1334_;
goto v_resetjp_1296_;
}
else
{
lean_dec(v_x_1285_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1334_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v_v_1299_; lean_object* v___x_1300_; lean_object* v_xs_x27_1301_; lean_object* v___y_1303_; 
v_v_1299_ = lean_array_fget(v_es_1290_, v_j_1293_);
v___x_1300_ = lean_box(0);
v_xs_x27_1301_ = lean_array_fset(v_es_1290_, v_j_1293_, v___x_1300_);
switch(lean_obj_tag(v_v_1299_))
{
case 0:
{
lean_object* v_key_1308_; lean_object* v_val_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1319_; 
v_key_1308_ = lean_ctor_get(v_v_1299_, 0);
v_val_1309_ = lean_ctor_get(v_v_1299_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_v_1299_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1311_ = v_v_1299_;
v_isShared_1312_ = v_isSharedCheck_1319_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_val_1309_);
lean_inc(v_key_1308_);
lean_dec(v_v_1299_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1319_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
uint8_t v___x_1313_; 
v___x_1313_ = l_Lean_instBEqMVarId_beq(v_x_1288_, v_key_1308_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_del_object(v___x_1311_);
v___x_1314_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1308_, v_val_1309_, v_x_1288_, v_x_1289_);
v___x_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
v___y_1303_ = v___x_1315_;
goto v___jp_1302_;
}
else
{
lean_object* v___x_1317_; 
lean_dec(v_val_1309_);
lean_dec(v_key_1308_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 1, v_x_1289_);
lean_ctor_set(v___x_1311_, 0, v_x_1288_);
v___x_1317_ = v___x_1311_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_x_1288_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_x_1289_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
v___y_1303_ = v___x_1317_;
goto v___jp_1302_;
}
}
}
}
case 1:
{
lean_object* v_node_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1332_; 
v_node_1320_ = lean_ctor_get(v_v_1299_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_v_1299_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1322_ = v_v_1299_;
v_isShared_1323_ = v_isSharedCheck_1332_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_node_1320_);
lean_dec(v_v_1299_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1332_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
size_t v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1324_ = ((size_t)5ULL);
v___x_1325_ = lean_usize_shift_right(v_x_1286_, v___x_1324_);
v___x_1326_ = ((size_t)1ULL);
v___x_1327_ = lean_usize_add(v_x_1287_, v___x_1326_);
v___x_1328_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_node_1320_, v___x_1325_, v___x_1327_, v_x_1288_, v_x_1289_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1328_);
v___x_1330_ = v___x_1322_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
v___y_1303_ = v___x_1330_;
goto v___jp_1302_;
}
}
}
default: 
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_x_1288_);
lean_ctor_set(v___x_1333_, 1, v_x_1289_);
v___y_1303_ = v___x_1333_;
goto v___jp_1302_;
}
}
v___jp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = lean_array_fset(v_xs_x27_1301_, v_j_1293_, v___y_1303_);
lean_dec(v_j_1293_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1304_);
v___x_1306_ = v___x_1297_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
else
{
lean_object* v_ks_1336_; lean_object* v_vs_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1355_; 
v_ks_1336_ = lean_ctor_get(v_x_1285_, 0);
v_vs_1337_ = lean_ctor_get(v_x_1285_, 1);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_x_1285_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1339_ = v_x_1285_;
v_isShared_1340_ = v_isSharedCheck_1355_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_vs_1337_);
lean_inc(v_ks_1336_);
lean_dec(v_x_1285_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1355_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_ks_1336_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_vs_1337_);
v___x_1342_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v_newNode_1343_; size_t v___x_1344_; uint8_t v___x_1345_; 
v_newNode_1343_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1342_, v_x_1288_, v_x_1289_);
v___x_1344_ = ((size_t)7ULL);
v___x_1345_ = lean_usize_dec_le(v___x_1344_, v_x_1287_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1346_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1343_);
v___x_1347_ = lean_unsigned_to_nat(4u);
v___x_1348_ = lean_nat_dec_lt(v___x_1346_, v___x_1347_);
lean_dec(v___x_1346_);
if (v___x_1348_ == 0)
{
lean_object* v_ks_1349_; lean_object* v_vs_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_ks_1349_ = lean_ctor_get(v_newNode_1343_, 0);
lean_inc_ref(v_ks_1349_);
v_vs_1350_ = lean_ctor_get(v_newNode_1343_, 1);
lean_inc_ref(v_vs_1350_);
lean_dec_ref(v_newNode_1343_);
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0);
v___x_1353_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1287_, v_ks_1349_, v_vs_1350_, v___x_1351_, v___x_1352_);
lean_dec_ref(v_vs_1350_);
lean_dec_ref(v_ks_1349_);
return v___x_1353_;
}
else
{
return v_newNode_1343_;
}
}
else
{
return v_newNode_1343_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1285_ = stack[0].m_obj;
size_t v_x_1286_ = stack[1].m_num;
size_t v_x_1287_ = stack[2].m_num;
lean_object* v_x_1288_ = stack[3].m_obj;
lean_object* v_x_1289_ = stack[4].m_obj;
lean_object* v_res_1356_;
v_res_1356_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1285_, v_x_1286_, v_x_1287_, v_x_1288_, v_x_1289_);
stack->m_obj
 = v_res_1356_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1357_, lean_object* v_keys_1358_, lean_object* v_vals_1359_, lean_object* v_i_1360_, lean_object* v_entries_1361_){
_start:
{
lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = lean_array_get_size(v_keys_1358_);
v___x_1363_ = lean_nat_dec_lt(v_i_1360_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_dec(v_i_1360_);
return v_entries_1361_;
}
else
{
lean_object* v_k_1364_; lean_object* v_v_1365_; uint64_t v___x_1366_; size_t v_h_1367_; size_t v___x_1368_; lean_object* v___x_1369_; size_t v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; size_t v_h_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_k_1364_ = lean_array_fget_borrowed(v_keys_1358_, v_i_1360_);
v_v_1365_ = lean_array_fget_borrowed(v_vals_1359_, v_i_1360_);
v___x_1366_ = l_Lean_instHashableMVarId_hash(v_k_1364_);
v_h_1367_ = lean_uint64_to_usize(v___x_1366_);
v___x_1368_ = ((size_t)5ULL);
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = ((size_t)1ULL);
v___x_1371_ = lean_usize_sub(v_depth_1357_, v___x_1370_);
v___x_1372_ = lean_usize_mul(v___x_1368_, v___x_1371_);
v_h_1373_ = lean_usize_shift_right(v_h_1367_, v___x_1372_);
v___x_1374_ = lean_nat_add(v_i_1360_, v___x_1369_);
lean_dec(v_i_1360_);
lean_inc(v_v_1365_);
lean_inc(v_k_1364_);
v___x_1375_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_entries_1361_, v_h_1373_, v_depth_1357_, v_k_1364_, v_v_1365_);
v_i_1360_ = v___x_1374_;
v_entries_1361_ = v___x_1375_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1357_ = stack[0].m_num;
lean_object* v_keys_1358_ = stack[1].m_obj;
lean_object* v_vals_1359_ = stack[2].m_obj;
lean_object* v_i_1360_ = stack[3].m_obj;
lean_object* v_entries_1361_ = stack[4].m_obj;
lean_object* v_res_1377_;
v_res_1377_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1357_, v_keys_1358_, v_vals_1359_, v_i_1360_, v_entries_1361_);
stack->m_obj
 = v_res_1377_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1378_, lean_object* v_keys_1379_, lean_object* v_vals_1380_, lean_object* v_i_1381_, lean_object* v_entries_1382_){
_start:
{
size_t v_depth_boxed_1383_; lean_object* v_res_1384_; 
v_depth_boxed_1383_ = lean_unbox_usize(v_depth_1378_);
lean_dec(v_depth_1378_);
v_res_1384_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1383_, v_keys_1379_, v_vals_1380_, v_i_1381_, v_entries_1382_);
lean_dec_ref(v_vals_1380_);
lean_dec_ref(v_keys_1379_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_){
_start:
{
size_t v_x_2294__boxed_1390_; size_t v_x_2295__boxed_1391_; lean_object* v_res_1392_; 
v_x_2294__boxed_1390_ = lean_unbox_usize(v_x_1386_);
lean_dec(v_x_1386_);
v_x_2295__boxed_1391_ = lean_unbox_usize(v_x_1387_);
lean_dec(v_x_1387_);
v_res_1392_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1385_, v_x_2294__boxed_1390_, v_x_2295__boxed_1391_, v_x_1388_, v_x_1389_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(lean_object* v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
uint64_t v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = l_Lean_instHashableMVarId_hash(v_x_1394_);
v___x_1397_ = lean_uint64_to_usize(v___x_1396_);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1393_, v___x_1397_, v___x_1398_, v_x_1394_, v_x_1395_);
return v___x_1399_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(lean_object* v_mvarId_1400_, lean_object* v_val_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v_mctx_1405_; lean_object* v_cache_1406_; lean_object* v_zetaDeltaFVarIds_1407_; lean_object* v_postponed_1408_; lean_object* v_diag_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1439_; 
v___x_1404_ = lean_st_ref_take(v___y_1402_);
v_mctx_1405_ = lean_ctor_get(v___x_1404_, 0);
v_cache_1406_ = lean_ctor_get(v___x_1404_, 1);
v_zetaDeltaFVarIds_1407_ = lean_ctor_get(v___x_1404_, 2);
v_postponed_1408_ = lean_ctor_get(v___x_1404_, 3);
v_diag_1409_ = lean_ctor_get(v___x_1404_, 4);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1411_ = v___x_1404_;
v_isShared_1412_ = v_isSharedCheck_1439_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_diag_1409_);
lean_inc(v_postponed_1408_);
lean_inc(v_zetaDeltaFVarIds_1407_);
lean_inc(v_cache_1406_);
lean_inc(v_mctx_1405_);
lean_dec(v___x_1404_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1439_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v_depth_1413_; lean_object* v_levelAssignDepth_1414_; lean_object* v_lmvarCounter_1415_; lean_object* v_mvarCounter_1416_; lean_object* v_lDecls_1417_; lean_object* v_decls_1418_; lean_object* v_userNames_1419_; lean_object* v_lAssignment_1420_; lean_object* v_eAssignment_1421_; lean_object* v_dAssignment_1422_; lean_object* v_instanceTypedMVars_1423_; lean_object* v_synthNormMemo_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1438_; 
v_depth_1413_ = lean_ctor_get(v_mctx_1405_, 0);
v_levelAssignDepth_1414_ = lean_ctor_get(v_mctx_1405_, 1);
v_lmvarCounter_1415_ = lean_ctor_get(v_mctx_1405_, 2);
v_mvarCounter_1416_ = lean_ctor_get(v_mctx_1405_, 3);
v_lDecls_1417_ = lean_ctor_get(v_mctx_1405_, 4);
v_decls_1418_ = lean_ctor_get(v_mctx_1405_, 5);
v_userNames_1419_ = lean_ctor_get(v_mctx_1405_, 6);
v_lAssignment_1420_ = lean_ctor_get(v_mctx_1405_, 7);
v_eAssignment_1421_ = lean_ctor_get(v_mctx_1405_, 8);
v_dAssignment_1422_ = lean_ctor_get(v_mctx_1405_, 9);
v_instanceTypedMVars_1423_ = lean_ctor_get(v_mctx_1405_, 10);
v_synthNormMemo_1424_ = lean_ctor_get(v_mctx_1405_, 11);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_mctx_1405_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1426_ = v_mctx_1405_;
v_isShared_1427_ = v_isSharedCheck_1438_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_synthNormMemo_1424_);
lean_inc(v_instanceTypedMVars_1423_);
lean_inc(v_dAssignment_1422_);
lean_inc(v_eAssignment_1421_);
lean_inc(v_lAssignment_1420_);
lean_inc(v_userNames_1419_);
lean_inc(v_decls_1418_);
lean_inc(v_lDecls_1417_);
lean_inc(v_mvarCounter_1416_);
lean_inc(v_lmvarCounter_1415_);
lean_inc(v_levelAssignDepth_1414_);
lean_inc(v_depth_1413_);
lean_dec(v_mctx_1405_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1438_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1428_ = lean_box(0);
v___x_1429_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_eAssignment_1421_, v_mvarId_1400_, v_val_1401_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 8, v___x_1429_);
v___x_1431_ = v___x_1426_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_depth_1413_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_levelAssignDepth_1414_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_lmvarCounter_1415_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v_mvarCounter_1416_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v_lDecls_1417_);
lean_ctor_set(v_reuseFailAlloc_1437_, 5, v_decls_1418_);
lean_ctor_set(v_reuseFailAlloc_1437_, 6, v_userNames_1419_);
lean_ctor_set(v_reuseFailAlloc_1437_, 7, v_lAssignment_1420_);
lean_ctor_set(v_reuseFailAlloc_1437_, 8, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1437_, 9, v_dAssignment_1422_);
lean_ctor_set(v_reuseFailAlloc_1437_, 10, v_instanceTypedMVars_1423_);
lean_ctor_set(v_reuseFailAlloc_1437_, 11, v_synthNormMemo_1424_);
v___x_1431_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1433_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1431_);
v___x_1433_ = v___x_1411_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_cache_1406_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_zetaDeltaFVarIds_1407_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v_postponed_1408_);
lean_ctor_set(v_reuseFailAlloc_1436_, 4, v_diag_1409_);
v___x_1433_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_st_ref_put(v___y_1402_, v___x_1433_);
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1428_);
return v___x_1435_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1400_ = stack[0].m_obj;
lean_object* v_val_1401_ = stack[1].m_obj;
lean_object* v___y_1402_ = stack[2].m_obj;
lean_object* v_res_1440_;
v_res_1440_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1400_, v_val_1401_, v___y_1402_);
stack->m_obj
 = v_res_1440_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg___boxed(lean_object* v_mvarId_1441_, lean_object* v_val_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1441_, v_val_1442_, v___y_1443_);
lean_dec(v___y_1443_);
return v_res_1445_;
}
}
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object* v_mvarId_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v___x_1454_; 
lean_inc(v_mvarId_1446_);
v___x_1454_ = l_Lean_MVarId_getDecl(v_mvarId_1446_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v_userName_1456_; lean_object* v_lctx_1457_; lean_object* v_type_1458_; lean_object* v_localInstances_1459_; lean_object* v___x_1460_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v_userName_1456_ = lean_ctor_get(v_a_1455_, 0);
lean_inc(v_userName_1456_);
v_lctx_1457_ = lean_ctor_get(v_a_1455_, 1);
lean_inc_ref(v_lctx_1457_);
v_type_1458_ = lean_ctor_get(v_a_1455_, 2);
lean_inc_ref(v_type_1458_);
v_localInstances_1459_ = lean_ctor_get(v_a_1455_, 4);
lean_inc_ref(v_localInstances_1459_);
lean_dec(v_a_1455_);
v___x_1460_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_1457_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = l_Lean_Meta_Sym_preprocessExpr(v_type_1458_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; uint8_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1464_ = 2;
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_1461_, v_localInstances_1459_, v_a_1463_, v___x_1464_, v_userName_1456_, v___x_1465_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1476_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc_n(v_a_1467_, 2);
lean_dec_ref_known(v___x_1466_, 1);
v___x_1468_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1446_, v_a_1467_, v_a_1450_);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v___x_1468_, 0);
lean_dec(v_unused_1477_);
v___x_1470_ = v___x_1468_;
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
else
{
lean_dec(v___x_1468_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = l_Lean_Expr_mvarId_x21(v_a_1467_);
lean_dec(v_a_1467_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v___x_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_mvarId_1446_);
v_a_1478_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1466_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1466_);
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
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec(v_a_1461_);
lean_dec_ref(v_localInstances_1459_);
lean_dec(v_userName_1456_);
lean_dec(v_mvarId_1446_);
v_a_1486_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1462_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1462_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v_localInstances_1459_);
lean_dec_ref(v_type_1458_);
lean_dec(v_userName_1456_);
lean_dec(v_mvarId_1446_);
v_a_1494_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1460_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1460_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v_mvarId_1446_);
v_a_1502_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1454_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1454_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_preprocessMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1446_ = stack[0].m_obj;
lean_object* v_a_1447_ = stack[1].m_obj;
lean_object* v_a_1448_ = stack[2].m_obj;
lean_object* v_a_1449_ = stack[3].m_obj;
lean_object* v_a_1450_ = stack[4].m_obj;
lean_object* v_a_1451_ = stack[5].m_obj;
lean_object* v_a_1452_ = stack[6].m_obj;
lean_object* v_res_1510_;
v_res_1510_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
stack->m_obj
 = v_res_1510_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar___boxed(lean_object* v_mvarId_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
return v_res_1519_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(lean_object* v_mvarId_1520_, lean_object* v_val_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1520_, v_val_1521_, v___y_1525_);
return v___x_1529_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1520_ = stack[0].m_obj;
lean_object* v_val_1521_ = stack[1].m_obj;
lean_object* v___y_1522_ = stack[2].m_obj;
lean_object* v___y_1523_ = stack[3].m_obj;
lean_object* v___y_1524_ = stack[4].m_obj;
lean_object* v___y_1525_ = stack[5].m_obj;
lean_object* v___y_1526_ = stack[6].m_obj;
lean_object* v___y_1527_ = stack[7].m_obj;
lean_object* v_res_1530_;
v_res_1530_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(v_mvarId_1520_, v_val_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
stack->m_obj
 = v_res_1530_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___boxed(lean_object* v_mvarId_1531_, lean_object* v_val_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(v_mvarId_1531_, v_val_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0(lean_object* v_00_u03b2_1541_, lean_object* v_x_1542_, lean_object* v_x_1543_, lean_object* v_x_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_x_1542_, v_x_1543_, v_x_1544_);
return v___x_1545_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1546_, lean_object* v_x_1547_, size_t v_x_1548_, size_t v_x_1549_, lean_object* v_x_1550_, lean_object* v_x_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1547_, v_x_1548_, v_x_1549_, v_x_1550_, v_x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1547_ = stack[1].m_obj;
size_t v_x_1548_ = stack[2].m_num;
size_t v_x_1549_ = stack[3].m_num;
lean_object* v_x_1550_ = stack[4].m_obj;
lean_object* v_x_1551_ = stack[5].m_obj;
lean_object* v_res_1553_;
v_res_1553_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(lean_box(0), v_x_1547_, v_x_1548_, v_x_1549_, v_x_1550_, v_x_1551_);
stack->m_obj
 = v_res_1553_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1554_, lean_object* v_x_1555_, lean_object* v_x_1556_, lean_object* v_x_1557_, lean_object* v_x_1558_, lean_object* v_x_1559_){
_start:
{
size_t v_x_2829__boxed_1560_; size_t v_x_2830__boxed_1561_; lean_object* v_res_1562_; 
v_x_2829__boxed_1560_ = lean_unbox_usize(v_x_1556_);
lean_dec(v_x_1556_);
v_x_2830__boxed_1561_ = lean_unbox_usize(v_x_1557_);
lean_dec(v_x_1557_);
v_res_1562_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(v_00_u03b2_1554_, v_x_1555_, v_x_2829__boxed_1560_, v_x_2830__boxed_1561_, v_x_1558_, v_x_1559_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1563_, lean_object* v_n_1564_, lean_object* v_k_1565_, lean_object* v_v_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1564_, v_k_1565_, v_v_1566_);
return v___x_1567_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1568_, size_t v_depth_1569_, lean_object* v_keys_1570_, lean_object* v_vals_1571_, lean_object* v_heq_1572_, lean_object* v_i_1573_, lean_object* v_entries_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1569_, v_keys_1570_, v_vals_1571_, v_i_1573_, v_entries_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1569_ = stack[1].m_num;
lean_object* v_keys_1570_ = stack[2].m_obj;
lean_object* v_vals_1571_ = stack[3].m_obj;
lean_object* v_i_1573_ = stack[5].m_obj;
lean_object* v_entries_1574_ = stack[6].m_obj;
lean_object* v_res_1576_;
v_res_1576_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_depth_1569_, v_keys_1570_, v_vals_1571_, lean_box(0), v_i_1573_, v_entries_1574_);
stack->m_obj
 = v_res_1576_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1577_, lean_object* v_depth_1578_, lean_object* v_keys_1579_, lean_object* v_vals_1580_, lean_object* v_heq_1581_, lean_object* v_i_1582_, lean_object* v_entries_1583_){
_start:
{
size_t v_depth_boxed_1584_; lean_object* v_res_1585_; 
v_depth_boxed_1584_ = lean_unbox_usize(v_depth_1578_);
lean_dec(v_depth_1578_);
v_res_1585_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1577_, v_depth_boxed_1584_, v_keys_1579_, v_vals_1580_, v_heq_1581_, v_i_1582_, v_entries_1583_);
lean_dec_ref(v_vals_1580_);
lean_dec_ref(v_keys_1579_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1586_, lean_object* v_x_1587_, lean_object* v_x_1588_, lean_object* v_x_1589_, lean_object* v_x_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1587_, v_x_1588_, v_x_1589_, v_x_1590_);
return v___x_1591_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(lean_object* v_msgData_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; lean_object* v_env_1599_; uint8_t v___x_1600_; lean_object* v_env_1601_; lean_object* v___x_1602_; lean_object* v_toCold_1603_; lean_object* v_mctx_1604_; lean_object* v_lctx_1605_; lean_object* v_options_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1598_ = lean_st_ref_get(v___y_1596_);
v_env_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc_ref(v_env_1599_);
lean_dec(v___x_1598_);
v___x_1600_ = 0;
v_env_1601_ = l_Lean_Environment_setRecordingDeps(v_env_1599_, v___x_1600_);
v___x_1602_ = lean_st_ref_get(v___y_1594_);
v_toCold_1603_ = lean_ctor_get(v___y_1595_, 0);
v_mctx_1604_ = lean_ctor_get(v___x_1602_, 0);
lean_inc_ref(v_mctx_1604_);
lean_dec(v___x_1602_);
v_lctx_1605_ = lean_ctor_get(v___y_1593_, 2);
v_options_1606_ = lean_ctor_get(v_toCold_1603_, 2);
lean_inc_ref(v_options_1606_);
lean_inc_ref(v_lctx_1605_);
v___x_1607_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1607_, 0, v_env_1601_);
lean_ctor_set(v___x_1607_, 1, v_mctx_1604_);
lean_ctor_set(v___x_1607_, 2, v_lctx_1605_);
lean_ctor_set(v___x_1607_, 3, v_options_1606_);
v___x_1608_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v_msgData_1592_);
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1592_ = stack[0].m_obj;
lean_object* v___y_1593_ = stack[1].m_obj;
lean_object* v___y_1594_ = stack[2].m_obj;
lean_object* v___y_1595_ = stack[3].m_obj;
lean_object* v___y_1596_ = stack[4].m_obj;
lean_object* v_res_1610_;
v_res_1610_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msgData_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
stack->m_obj
 = v_res_1610_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0___boxed(lean_object* v_msgData_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msgData_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
return v_res_1617_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(lean_object* v_msg_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_ref_1624_; lean_object* v___x_1625_; lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1634_; 
v_ref_1624_ = lean_ctor_get(v___y_1621_, 2);
v___x_1625_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msg_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1634_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1634_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1632_; 
lean_inc(v_ref_1624_);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v_ref_1624_);
lean_ctor_set(v___x_1630_, 1, v_a_1626_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 1);
lean_ctor_set(v___x_1628_, 0, v___x_1630_);
v___x_1632_ = v___x_1628_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1618_ = stack[0].m_obj;
lean_object* v___y_1619_ = stack[1].m_obj;
lean_object* v___y_1620_ = stack[2].m_obj;
lean_object* v___y_1621_ = stack[3].m_obj;
lean_object* v___y_1622_ = stack[4].m_obj;
lean_object* v_res_1635_;
v_res_1635_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
stack->m_obj
 = v_res_1635_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(lean_object* v_msg_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
return v_res_1642_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0));
v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
return v___x_1645_;
}
}
lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(lean_object* v_msg_1649_, lean_object* v_e_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v___y_1659_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___x_1666_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2));
v___x_1667_ = lean_string_dec_eq(v_msg_1649_, v___x_1666_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1668_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3));
v___x_1669_ = lean_string_append(v___x_1668_, v_msg_1649_);
lean_dec_ref(v_msg_1649_);
v___x_1670_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4));
v___x_1671_ = lean_string_append(v___x_1669_, v___x_1670_);
v___y_1659_ = v___x_1671_;
goto v___jp_1658_;
}
else
{
v___y_1659_ = v_msg_1649_;
goto v___jp_1658_;
}
v___jp_1658_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1660_ = l_Lean_stringToMessageData(v___y_1659_);
v___x_1661_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1);
v___x_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = l_Lean_indentExpr(v_e_1650_);
v___x_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v___x_1664_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
return v___x_1665_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1649_ = stack[0].m_obj;
lean_object* v_e_1650_ = stack[1].m_obj;
lean_object* v_a_1651_ = stack[2].m_obj;
lean_object* v_a_1652_ = stack[3].m_obj;
lean_object* v_a_1653_ = stack[4].m_obj;
lean_object* v_a_1654_ = stack[5].m_obj;
lean_object* v_a_1655_ = stack[6].m_obj;
lean_object* v_a_1656_ = stack[7].m_obj;
lean_object* v_res_1672_;
v_res_1672_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1649_, v_e_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
stack->m_obj
 = v_res_1672_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(lean_object* v_msg_1673_, lean_object* v_e_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1673_, v_e_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
return v_res_1682_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_object* v_00_u03b1_1683_, lean_object* v_msg_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_1684_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1684_ = stack[1].m_obj;
lean_object* v___y_1685_ = stack[2].m_obj;
lean_object* v___y_1686_ = stack[3].m_obj;
lean_object* v___y_1687_ = stack[4].m_obj;
lean_object* v___y_1688_ = stack[5].m_obj;
lean_object* v___y_1689_ = stack[6].m_obj;
lean_object* v___y_1690_ = stack[7].m_obj;
lean_object* v_res_1693_;
v_res_1693_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_box(0), v_msg_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
stack->m_obj
 = v_res_1693_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(lean_object* v_00_u03b1_1694_, lean_object* v_msg_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(v_00_u03b1_1694_, v_msg_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1704_, lean_object* v_vals_1705_, lean_object* v_i_1706_, lean_object* v_k_1707_){
_start:
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = lean_array_get_size(v_keys_1704_);
v___x_1709_ = lean_nat_dec_lt(v_i_1706_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; 
lean_dec(v_i_1706_);
v___x_1710_ = lean_box(0);
return v___x_1710_;
}
else
{
lean_object* v_k_x27_1711_; uint8_t v___x_1712_; 
v_k_x27_1711_ = lean_array_fget_borrowed(v_keys_1704_, v_i_1706_);
v___x_1712_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_1707_, v_k_x27_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_unsigned_to_nat(1u);
v___x_1714_ = lean_nat_add(v_i_1706_, v___x_1713_);
lean_dec(v_i_1706_);
v_i_1706_ = v___x_1714_;
goto _start;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = lean_array_fget_borrowed(v_vals_1705_, v_i_1706_);
lean_dec(v_i_1706_);
lean_inc(v___x_1716_);
lean_inc(v_k_x27_1711_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_k_x27_1711_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
return v___x_1718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1719_, lean_object* v_vals_1720_, lean_object* v_i_1721_, lean_object* v_k_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_1719_, v_vals_1720_, v_i_1721_, v_k_1722_);
lean_dec_ref(v_k_1722_);
lean_dec_ref(v_vals_1720_);
lean_dec_ref(v_keys_1719_);
return v_res_1723_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(lean_object* v_x_1724_, size_t v_x_1725_, lean_object* v_x_1726_){
_start:
{
if (lean_obj_tag(v_x_1724_) == 0)
{
lean_object* v_es_1727_; lean_object* v___x_1728_; size_t v___x_1729_; size_t v___x_1730_; lean_object* v_j_1731_; lean_object* v___x_1732_; 
v_es_1727_ = lean_ctor_get(v_x_1724_, 0);
v___x_1728_ = lean_box(2);
v___x_1729_ = ((size_t)31ULL);
v___x_1730_ = lean_usize_land(v_x_1725_, v___x_1729_);
v_j_1731_ = lean_usize_to_nat(v___x_1730_);
v___x_1732_ = lean_array_get_borrowed(v___x_1728_, v_es_1727_, v_j_1731_);
lean_dec(v_j_1731_);
switch(lean_obj_tag(v___x_1732_))
{
case 0:
{
lean_object* v_key_1733_; lean_object* v_val_1734_; uint8_t v___x_1735_; 
v_key_1733_ = lean_ctor_get(v___x_1732_, 0);
v_val_1734_ = lean_ctor_get(v___x_1732_, 1);
v___x_1735_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_1726_, v_key_1733_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_box(0);
return v___x_1736_;
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_inc(v_val_1734_);
lean_inc(v_key_1733_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v_key_1733_);
lean_ctor_set(v___x_1737_, 1, v_val_1734_);
v___x_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
}
case 1:
{
lean_object* v_node_1739_; size_t v___x_1740_; size_t v___x_1741_; 
v_node_1739_ = lean_ctor_get(v___x_1732_, 0);
v___x_1740_ = ((size_t)5ULL);
v___x_1741_ = lean_usize_shift_right(v_x_1725_, v___x_1740_);
v_x_1724_ = v_node_1739_;
v_x_1725_ = v___x_1741_;
goto _start;
}
default: 
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_box(0);
return v___x_1743_;
}
}
}
else
{
lean_object* v_ks_1744_; lean_object* v_vs_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_ks_1744_ = lean_ctor_get(v_x_1724_, 0);
v_vs_1745_ = lean_ctor_get(v_x_1724_, 1);
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_ks_1744_, v_vs_1745_, v___x_1746_, v_x_1726_);
return v___x_1747_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1724_ = stack[0].m_obj;
size_t v_x_1725_ = stack[1].m_num;
lean_object* v_x_1726_ = stack[2].m_obj;
lean_object* v_res_1748_;
v_res_1748_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_1724_, v_x_1725_, v_x_1726_);
stack->m_obj
 = v_res_1748_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_){
_start:
{
size_t v_x_7396__boxed_1752_; lean_object* v_res_1753_; 
v_x_7396__boxed_1752_ = lean_unbox_usize(v_x_1750_);
lean_dec(v_x_1750_);
v_res_1753_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_1749_, v_x_7396__boxed_1752_, v_x_1751_);
lean_dec_ref(v_x_1751_);
lean_dec_ref(v_x_1749_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(lean_object* v_x_1754_, lean_object* v_x_1755_){
_start:
{
uint64_t v___x_1756_; size_t v___x_1757_; lean_object* v___x_1758_; 
v___x_1756_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_1755_);
v___x_1757_ = lean_uint64_to_usize(v___x_1756_);
v___x_1758_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_1754_, v___x_1757_, v_x_1755_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg___boxed(lean_object* v_x_1759_, lean_object* v_x_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_1759_, v_x_1760_);
lean_dec_ref(v_x_1760_);
lean_dec_ref(v_x_1759_);
return v_res_1761_;
}
}
lean_object* l_Lean_Expr_checkMaxShared___lam__0(lean_object* v_msg_1762_, lean_object* v_e_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___y_1776_; lean_object* v___x_1785_; lean_object* v_share_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_st_ref_get(v___y_1765_);
v_share_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc_ref(v_share_1786_);
lean_dec(v___x_1785_);
v___x_1787_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_share_1786_, v_e_1763_);
lean_dec_ref(v_share_1786_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v___x_1788_; 
v___x_1788_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1762_, v_e_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
v___y_1776_ = v___x_1788_;
goto v___jp_1775_;
}
else
{
lean_object* v_val_1789_; lean_object* v_fst_1790_; size_t v___x_1791_; size_t v___x_1792_; uint8_t v___x_1793_; 
v_val_1789_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_val_1789_);
lean_dec_ref_known(v___x_1787_, 1);
v_fst_1790_ = lean_ctor_get(v_val_1789_, 0);
lean_inc(v_fst_1790_);
lean_dec(v_val_1789_);
v___x_1791_ = lean_ptr_addr(v_fst_1790_);
lean_dec(v_fst_1790_);
v___x_1792_ = lean_ptr_addr(v_e_1763_);
v___x_1793_ = lean_usize_dec_eq(v___x_1791_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; 
v___x_1794_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1762_, v_e_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
v___y_1776_ = v___x_1794_;
goto v___jp_1775_;
}
else
{
lean_dec_ref(v_e_1763_);
lean_dec_ref(v_msg_1762_);
goto v___jp_1771_;
}
}
v___jp_1771_:
{
uint8_t v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = 1;
v___x_1773_ = lean_box(v___x_1772_);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
return v___x_1774_;
}
v___jp_1775_:
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
v_a_1777_ = lean_ctor_get(v___y_1776_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___y_1776_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___y_1776_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___y_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_checkMaxShared___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1762_ = stack[0].m_obj;
lean_object* v_e_1763_ = stack[1].m_obj;
lean_object* v___y_1764_ = stack[2].m_obj;
lean_object* v___y_1765_ = stack[3].m_obj;
lean_object* v___y_1766_ = stack[4].m_obj;
lean_object* v___y_1767_ = stack[5].m_obj;
lean_object* v___y_1768_ = stack[6].m_obj;
lean_object* v___y_1769_ = stack[7].m_obj;
lean_object* v_res_1795_;
v_res_1795_ = l_Lean_Expr_checkMaxShared___lam__0(v_msg_1762_, v_e_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
stack->m_obj
 = v_res_1795_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0___boxed(lean_object* v_msg_1796_, lean_object* v_e_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Expr_checkMaxShared___lam__0(v_msg_1796_, v_e_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(lean_object* v_a_1806_, lean_object* v_x_1807_){
_start:
{
if (lean_obj_tag(v_x_1807_) == 0)
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_box(0);
return v___x_1808_;
}
else
{
lean_object* v_key_1809_; lean_object* v_value_1810_; lean_object* v_tail_1811_; uint8_t v___x_1812_; 
v_key_1809_ = lean_ctor_get(v_x_1807_, 0);
v_value_1810_ = lean_ctor_get(v_x_1807_, 1);
v_tail_1811_ = lean_ctor_get(v_x_1807_, 2);
v___x_1812_ = lean_expr_eqv(v_key_1809_, v_a_1806_);
if (v___x_1812_ == 0)
{
v_x_1807_ = v_tail_1811_;
goto _start;
}
else
{
lean_object* v___x_1814_; 
lean_inc(v_value_1810_);
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v_value_1810_);
return v___x_1814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_1815_, lean_object* v_x_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_1815_, v_x_1816_);
lean_dec(v_x_1816_);
lean_dec_ref(v_a_1815_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(lean_object* v_m_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_buckets_1820_; lean_object* v___x_1821_; uint64_t v___x_1822_; uint64_t v___x_1823_; uint64_t v___x_1824_; uint64_t v_fold_1825_; uint64_t v___x_1826_; uint64_t v___x_1827_; uint64_t v___x_1828_; size_t v___x_1829_; size_t v___x_1830_; size_t v___x_1831_; size_t v___x_1832_; size_t v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_buckets_1820_ = lean_ctor_get(v_m_1818_, 1);
v___x_1821_ = lean_array_get_size(v_buckets_1820_);
v___x_1822_ = l_Lean_Expr_hash(v_a_1819_);
v___x_1823_ = 32ULL;
v___x_1824_ = lean_uint64_shift_right(v___x_1822_, v___x_1823_);
v_fold_1825_ = lean_uint64_xor(v___x_1822_, v___x_1824_);
v___x_1826_ = 16ULL;
v___x_1827_ = lean_uint64_shift_right(v_fold_1825_, v___x_1826_);
v___x_1828_ = lean_uint64_xor(v_fold_1825_, v___x_1827_);
v___x_1829_ = lean_uint64_to_usize(v___x_1828_);
v___x_1830_ = lean_usize_of_nat(v___x_1821_);
v___x_1831_ = ((size_t)1ULL);
v___x_1832_ = lean_usize_sub(v___x_1830_, v___x_1831_);
v___x_1833_ = lean_usize_land(v___x_1829_, v___x_1832_);
v___x_1834_ = lean_array_uget_borrowed(v_buckets_1820_, v___x_1833_);
v___x_1835_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_1819_, v___x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(lean_object* v_m_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_1836_, v_a_1837_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_m_1836_);
return v_res_1838_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(lean_object* v_a_1839_, lean_object* v_x_1840_){
_start:
{
if (lean_obj_tag(v_x_1840_) == 0)
{
uint8_t v___x_1841_; 
v___x_1841_ = 0;
return v___x_1841_;
}
else
{
lean_object* v_key_1842_; lean_object* v_tail_1843_; uint8_t v___x_1844_; 
v_key_1842_ = lean_ctor_get(v_x_1840_, 0);
v_tail_1843_ = lean_ctor_get(v_x_1840_, 2);
v___x_1844_ = lean_expr_eqv(v_key_1842_, v_a_1839_);
if (v___x_1844_ == 0)
{
v_x_1840_ = v_tail_1843_;
goto _start;
}
else
{
return v___x_1844_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1839_ = stack[0].m_obj;
lean_object* v_x_1840_ = stack[1].m_obj;
uint8_t v_res_1846_;
v_res_1846_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_1839_, v_x_1840_);
stack->m_num = v_res_1846_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_a_1847_, lean_object* v_x_1848_){
_start:
{
uint8_t v_res_1849_; lean_object* v_r_1850_; 
v_res_1849_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_1847_, v_x_1848_);
lean_dec(v_x_1848_);
lean_dec_ref(v_a_1847_);
v_r_1850_ = lean_box(v_res_1849_);
return v_r_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(lean_object* v_a_1851_, lean_object* v_b_1852_, lean_object* v_x_1853_){
_start:
{
if (lean_obj_tag(v_x_1853_) == 0)
{
lean_dec(v_b_1852_);
lean_dec_ref(v_a_1851_);
return v_x_1853_;
}
else
{
lean_object* v_key_1854_; lean_object* v_value_1855_; lean_object* v_tail_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1868_; 
v_key_1854_ = lean_ctor_get(v_x_1853_, 0);
v_value_1855_ = lean_ctor_get(v_x_1853_, 1);
v_tail_1856_ = lean_ctor_get(v_x_1853_, 2);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_x_1853_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1858_ = v_x_1853_;
v_isShared_1859_ = v_isSharedCheck_1868_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_tail_1856_);
lean_inc(v_value_1855_);
lean_inc(v_key_1854_);
lean_dec(v_x_1853_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1868_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_expr_eqv(v_key_1854_, v_a_1851_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1861_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_1851_, v_b_1852_, v_tail_1856_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 2, v___x_1861_);
v___x_1863_ = v___x_1858_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_key_1854_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_value_1855_);
lean_ctor_set(v_reuseFailAlloc_1864_, 2, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
else
{
lean_object* v___x_1866_; 
lean_dec(v_value_1855_);
lean_dec(v_key_1854_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v_b_1852_);
lean_ctor_set(v___x_1858_, 0, v_a_1851_);
v___x_1866_ = v___x_1858_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1851_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_b_1852_);
lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_tail_1856_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(lean_object* v_x_1869_, lean_object* v_x_1870_){
_start:
{
if (lean_obj_tag(v_x_1870_) == 0)
{
return v_x_1869_;
}
else
{
lean_object* v_key_1871_; lean_object* v_value_1872_; lean_object* v_tail_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1896_; 
v_key_1871_ = lean_ctor_get(v_x_1870_, 0);
v_value_1872_ = lean_ctor_get(v_x_1870_, 1);
v_tail_1873_ = lean_ctor_get(v_x_1870_, 2);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_x_1870_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1875_ = v_x_1870_;
v_isShared_1876_ = v_isSharedCheck_1896_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_tail_1873_);
lean_inc(v_value_1872_);
lean_inc(v_key_1871_);
lean_dec(v_x_1870_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1896_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; uint64_t v___x_1878_; uint64_t v___x_1879_; uint64_t v___x_1880_; uint64_t v_fold_1881_; uint64_t v___x_1882_; uint64_t v___x_1883_; uint64_t v___x_1884_; size_t v___x_1885_; size_t v___x_1886_; size_t v___x_1887_; size_t v___x_1888_; size_t v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1877_ = lean_array_get_size(v_x_1869_);
v___x_1878_ = l_Lean_Expr_hash(v_key_1871_);
v___x_1879_ = 32ULL;
v___x_1880_ = lean_uint64_shift_right(v___x_1878_, v___x_1879_);
v_fold_1881_ = lean_uint64_xor(v___x_1878_, v___x_1880_);
v___x_1882_ = 16ULL;
v___x_1883_ = lean_uint64_shift_right(v_fold_1881_, v___x_1882_);
v___x_1884_ = lean_uint64_xor(v_fold_1881_, v___x_1883_);
v___x_1885_ = lean_uint64_to_usize(v___x_1884_);
v___x_1886_ = lean_usize_of_nat(v___x_1877_);
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = lean_usize_sub(v___x_1886_, v___x_1887_);
v___x_1889_ = lean_usize_land(v___x_1885_, v___x_1888_);
v___x_1890_ = lean_array_uget_borrowed(v_x_1869_, v___x_1889_);
lean_inc(v___x_1890_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 2, v___x_1890_);
v___x_1892_ = v___x_1875_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_key_1871_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_value_1872_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_array_uset(v_x_1869_, v___x_1889_, v___x_1892_);
v_x_1869_ = v___x_1893_;
v_x_1870_ = v_tail_1873_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(lean_object* v_i_1897_, lean_object* v_source_1898_, lean_object* v_target_1899_){
_start:
{
lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = lean_array_get_size(v_source_1898_);
v___x_1901_ = lean_nat_dec_lt(v_i_1897_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_dec_ref(v_source_1898_);
lean_dec(v_i_1897_);
return v_target_1899_;
}
else
{
lean_object* v_es_1902_; lean_object* v___x_1903_; lean_object* v_source_1904_; lean_object* v_target_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v_es_1902_ = lean_array_fget(v_source_1898_, v_i_1897_);
v___x_1903_ = lean_box(0);
v_source_1904_ = lean_array_fset(v_source_1898_, v_i_1897_, v___x_1903_);
v_target_1905_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_target_1899_, v_es_1902_);
v___x_1906_ = lean_unsigned_to_nat(1u);
v___x_1907_ = lean_nat_add(v_i_1897_, v___x_1906_);
lean_dec(v_i_1897_);
v_i_1897_ = v___x_1907_;
v_source_1898_ = v_source_1904_;
v_target_1899_ = v_target_1905_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(lean_object* v_data_1909_){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v_nbuckets_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1910_ = lean_array_get_size(v_data_1909_);
v___x_1911_ = lean_unsigned_to_nat(2u);
v_nbuckets_1912_ = lean_nat_mul(v___x_1910_, v___x_1911_);
v___x_1913_ = lean_unsigned_to_nat(0u);
v___x_1914_ = lean_box(0);
v___x_1915_ = lean_mk_array(v_nbuckets_1912_, v___x_1914_);
v___x_1916_ = lean_array_propagate_mark(v_data_1909_, v___x_1915_);
v___x_1917_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v___x_1913_, v_data_1909_, v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(lean_object* v_m_1918_, lean_object* v_a_1919_, lean_object* v_b_1920_){
_start:
{
lean_object* v_size_1921_; lean_object* v_buckets_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1965_; 
v_size_1921_ = lean_ctor_get(v_m_1918_, 0);
v_buckets_1922_ = lean_ctor_get(v_m_1918_, 1);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_m_1918_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1924_ = v_m_1918_;
v_isShared_1925_ = v_isSharedCheck_1965_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_buckets_1922_);
lean_inc(v_size_1921_);
lean_dec(v_m_1918_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1965_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; uint64_t v___x_1927_; uint64_t v___x_1928_; uint64_t v___x_1929_; uint64_t v_fold_1930_; uint64_t v___x_1931_; uint64_t v___x_1932_; uint64_t v___x_1933_; size_t v___x_1934_; size_t v___x_1935_; size_t v___x_1936_; size_t v___x_1937_; size_t v___x_1938_; lean_object* v_bkt_1939_; uint8_t v___x_1940_; 
v___x_1926_ = lean_array_get_size(v_buckets_1922_);
v___x_1927_ = l_Lean_Expr_hash(v_a_1919_);
v___x_1928_ = 32ULL;
v___x_1929_ = lean_uint64_shift_right(v___x_1927_, v___x_1928_);
v_fold_1930_ = lean_uint64_xor(v___x_1927_, v___x_1929_);
v___x_1931_ = 16ULL;
v___x_1932_ = lean_uint64_shift_right(v_fold_1930_, v___x_1931_);
v___x_1933_ = lean_uint64_xor(v_fold_1930_, v___x_1932_);
v___x_1934_ = lean_uint64_to_usize(v___x_1933_);
v___x_1935_ = lean_usize_of_nat(v___x_1926_);
v___x_1936_ = ((size_t)1ULL);
v___x_1937_ = lean_usize_sub(v___x_1935_, v___x_1936_);
v___x_1938_ = lean_usize_land(v___x_1934_, v___x_1937_);
v_bkt_1939_ = lean_array_uget_borrowed(v_buckets_1922_, v___x_1938_);
v___x_1940_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_1919_, v_bkt_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; lean_object* v_size_x27_1942_; lean_object* v___x_1943_; lean_object* v_buckets_x27_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1941_ = lean_unsigned_to_nat(1u);
v_size_x27_1942_ = lean_nat_add(v_size_1921_, v___x_1941_);
lean_dec(v_size_1921_);
lean_inc(v_bkt_1939_);
v___x_1943_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1943_, 0, v_a_1919_);
lean_ctor_set(v___x_1943_, 1, v_b_1920_);
lean_ctor_set(v___x_1943_, 2, v_bkt_1939_);
v_buckets_x27_1944_ = lean_array_uset(v_buckets_1922_, v___x_1938_, v___x_1943_);
v___x_1945_ = lean_unsigned_to_nat(4u);
v___x_1946_ = lean_nat_mul(v_size_x27_1942_, v___x_1945_);
v___x_1947_ = lean_unsigned_to_nat(3u);
v___x_1948_ = lean_nat_div(v___x_1946_, v___x_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_array_get_size(v_buckets_x27_1944_);
v___x_1950_ = lean_nat_dec_le(v___x_1948_, v___x_1949_);
lean_dec(v___x_1948_);
if (v___x_1950_ == 0)
{
lean_object* v_val_1951_; lean_object* v___x_1953_; 
v_val_1951_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_buckets_x27_1944_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v_val_1951_);
lean_ctor_set(v___x_1924_, 0, v_size_x27_1942_);
v___x_1953_ = v___x_1924_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_size_x27_1942_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_val_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
else
{
lean_object* v___x_1956_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v_buckets_x27_1944_);
lean_ctor_set(v___x_1924_, 0, v_size_x27_1942_);
v___x_1956_ = v___x_1924_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_size_x27_1942_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_buckets_x27_1944_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
else
{
lean_object* v___x_1958_; lean_object* v_buckets_x27_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
lean_inc(v_bkt_1939_);
v___x_1958_ = lean_box(0);
v_buckets_x27_1959_ = lean_array_uset(v_buckets_1922_, v___x_1938_, v___x_1958_);
v___x_1960_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_1919_, v_b_1920_, v_bkt_1939_);
v___x_1961_ = lean_array_uset(v_buckets_x27_1959_, v___x_1938_, v___x_1960_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v___x_1961_);
v___x_1963_ = v___x_1924_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_size_1921_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(lean_object* v_g_1966_, lean_object* v_e_1967_, lean_object* v_a_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_a_1977_; lean_object* v___y_1983_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = lean_st_ref_get(v_a_1968_);
v___x_1986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v___x_1985_, v_e_1967_);
lean_dec(v___x_1985_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v___x_1987_; 
lean_inc_ref(v_g_1966_);
lean_inc(v___y_1974_);
lean_inc_ref(v___y_1973_);
lean_inc(v___y_1972_);
lean_inc_ref(v___y_1971_);
lean_inc(v___y_1970_);
lean_inc_ref(v___y_1969_);
lean_inc_ref(v_e_1967_);
v___x_1987_ = lean_apply_8(v_g_1966_, v_e_1967_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, lean_box(0));
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v_d_1990_; lean_object* v_b_1991_; lean_object* v___y_1992_; uint8_t v___x_1995_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v___x_1995_ = lean_unbox(v_a_1988_);
lean_dec(v_a_1988_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
lean_dec_ref(v_g_1966_);
v___x_1996_ = lean_box(0);
v_a_1977_ = v___x_1996_;
goto v___jp_1976_;
}
else
{
switch(lean_obj_tag(v_e_1967_))
{
case 7:
{
lean_object* v_binderType_1997_; lean_object* v_body_1998_; 
v_binderType_1997_ = lean_ctor_get(v_e_1967_, 1);
v_body_1998_ = lean_ctor_get(v_e_1967_, 2);
lean_inc_ref(v_body_1998_);
lean_inc_ref(v_binderType_1997_);
v_d_1990_ = v_binderType_1997_;
v_b_1991_ = v_body_1998_;
v___y_1992_ = v_a_1968_;
goto v___jp_1989_;
}
case 6:
{
lean_object* v_binderType_1999_; lean_object* v_body_2000_; 
v_binderType_1999_ = lean_ctor_get(v_e_1967_, 1);
v_body_2000_ = lean_ctor_get(v_e_1967_, 2);
lean_inc_ref(v_body_2000_);
lean_inc_ref(v_binderType_1999_);
v_d_1990_ = v_binderType_1999_;
v_b_1991_ = v_body_2000_;
v___y_1992_ = v_a_1968_;
goto v___jp_1989_;
}
case 8:
{
lean_object* v_type_2001_; lean_object* v_value_2002_; lean_object* v_body_2003_; lean_object* v___x_2004_; 
v_type_2001_ = lean_ctor_get(v_e_1967_, 1);
v_value_2002_ = lean_ctor_get(v_e_1967_, 2);
v_body_2003_ = lean_ctor_get(v_e_1967_, 3);
lean_inc_ref(v_type_2001_);
lean_inc_ref(v_g_1966_);
v___x_2004_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1966_, v_type_2001_, v_a_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v___x_2005_; 
lean_dec_ref_known(v___x_2004_, 1);
lean_inc_ref(v_value_2002_);
lean_inc_ref(v_g_1966_);
v___x_2005_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1966_, v_value_2002_, v_a_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v___x_2006_; 
lean_dec_ref_known(v___x_2005_, 1);
lean_inc_ref(v_body_2003_);
v___x_2006_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1966_, v_body_2003_, v_a_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
v___y_1983_ = v___x_2006_;
goto v___jp_1982_;
}
else
{
lean_dec_ref(v_g_1966_);
v___y_1983_ = v___x_2005_;
goto v___jp_1982_;
}
}
else
{
lean_dec_ref(v_g_1966_);
v___y_1983_ = v___x_2004_;
goto v___jp_1982_;
}
}
case 5:
{
lean_object* v_fn_2007_; lean_object* v_arg_2008_; lean_object* v___x_2009_; 
v_fn_2007_ = lean_ctor_get(v_e_1967_, 0);
v_arg_2008_ = lean_ctor_get(v_e_1967_, 1);
lean_inc_ref(v_fn_2007_);
lean_inc_ref(v_g_1966_);
v___x_2009_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1966_, v_fn_2007_, v_a_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v___x_2010_; 
lean_dec_ref_known(v___x_2009_, 1);
lean_inc_ref(v_arg_2008_);
v___x_2010_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1966_, v_arg_2008_, v_a_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
v___y_1983_ = v___x_2010_;
goto v___jp_1982_;
}
else
{
lean_dec_ref(v_g_1966_);
v___y_1983_ = v___x_2009_;
goto v___jp_1982_;
}
}
case 10:
{
lean_object* v_expr_2011_; lean_object* v___x_2012_; 
v_expr_2011_ = lean_ctor_get(v_e_1967_, 1);
lean_inc_ref(v_expr_2011_);
v___x_2012_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1966_, v_expr_2011_, v_a_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
v___y_1983_ = v___x_2012_;
goto v___jp_1982_;
}
case 11:
{
lean_object* v_struct_2013_; lean_object* v___x_2014_; 
v_struct_2013_ = lean_ctor_get(v_e_1967_, 2);
lean_inc_ref(v_struct_2013_);
v___x_2014_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1966_, v_struct_2013_, v_a_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
v___y_1983_ = v___x_2014_;
goto v___jp_1982_;
}
default: 
{
lean_object* v___x_2015_; 
lean_dec_ref(v_g_1966_);
v___x_2015_ = lean_box(0);
v_a_1977_ = v___x_2015_;
goto v___jp_1976_;
}
}
}
v___jp_1989_:
{
lean_object* v___x_1993_; 
lean_inc_ref(v_g_1966_);
v___x_1993_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1966_, v_d_1990_, v___y_1992_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v___x_1994_; 
lean_dec_ref_known(v___x_1993_, 1);
v___x_1994_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1966_, v_b_1991_, v___y_1992_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
v___y_1983_ = v___x_1994_;
goto v___jp_1982_;
}
else
{
lean_dec_ref(v_b_1991_);
lean_dec_ref(v_g_1966_);
v___y_1983_ = v___x_1993_;
goto v___jp_1982_;
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref(v_e_1967_);
lean_dec_ref(v_g_1966_);
v_a_2016_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1987_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1987_);
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
lean_object* v_val_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref(v_e_1967_);
lean_dec_ref(v_g_1966_);
v_val_2024_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_1986_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_val_2024_);
lean_dec(v___x_1986_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set_tag(v___x_2026_, 0);
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_val_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
v___jp_1976_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1978_ = lean_st_ref_take(v_a_1968_);
v___x_1979_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v___x_1978_, v_e_1967_, v_a_1977_);
v___x_1980_ = lean_st_ref_put(v_a_1968_, v___x_1979_);
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v_a_1977_);
return v___x_1981_;
}
v___jp_1982_:
{
if (lean_obj_tag(v___y_1983_) == 0)
{
lean_object* v_a_1984_; 
v_a_1984_ = lean_ctor_get(v___y_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___y_1983_, 1);
v_a_1977_ = v_a_1984_;
goto v___jp_1976_;
}
else
{
lean_dec_ref(v_e_1967_);
return v___y_1983_;
}
}
}
}
LEAN_EXPORT void l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_1966_ = stack[0].m_obj;
lean_object* v_e_1967_ = stack[1].m_obj;
lean_object* v_a_1968_ = stack[2].m_obj;
lean_object* v___y_1969_ = stack[3].m_obj;
lean_object* v___y_1970_ = stack[4].m_obj;
lean_object* v___y_1971_ = stack[5].m_obj;
lean_object* v___y_1972_ = stack[6].m_obj;
lean_object* v___y_1973_ = stack[7].m_obj;
lean_object* v___y_1974_ = stack[8].m_obj;
lean_object* v_res_2032_;
v_res_2032_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1966_, v_e_1967_, v_a_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
stack->m_obj
 = v_res_2032_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(lean_object* v_g_2033_, lean_object* v_e_2034_, lean_object* v_a_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_2033_, v_e_2034_, v_a_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v_a_2035_);
return v_res_2043_;
}
}
static lean_object* _init_l_Lean_Expr_checkMaxShared___closed__0(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_unsigned_to_nat(16u);
v___x_2046_ = lean_mk_array(v___x_2045_, v___x_2044_);
return v___x_2046_;
}
}
static lean_object* _init_l_Lean_Expr_checkMaxShared___closed__1(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__0, &l_Lean_Expr_checkMaxShared___closed__0_once, _init_l_Lean_Expr_checkMaxShared___closed__0);
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v___x_2047_);
return v___x_2049_;
}
}
lean_object* l_Lean_Expr_checkMaxShared(lean_object* v_e_2050_, lean_object* v_msg_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v___f_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___f_2059_ = lean_alloc_closure((void*)(l_Lean_Expr_checkMaxShared___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2059_, 0, v_msg_2051_);
v___x_2060_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__1, &l_Lean_Expr_checkMaxShared___closed__1_once, _init_l_Lean_Expr_checkMaxShared___closed__1);
v___x_2061_ = lean_st_mk_ref(v___x_2060_);
v___x_2062_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v___f_2059_, v_e_2050_, v___x_2061_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2071_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_st_ref_get(v___x_2061_);
lean_dec(v___x_2061_);
lean_dec(v___x_2067_);
if (v_isShared_2066_ == 0)
{
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2063_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
else
{
lean_dec(v___x_2061_);
return v___x_2062_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_checkMaxShared_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2050_ = stack[0].m_obj;
lean_object* v_msg_2051_ = stack[1].m_obj;
lean_object* v_a_2052_ = stack[2].m_obj;
lean_object* v_a_2053_ = stack[3].m_obj;
lean_object* v_a_2054_ = stack[4].m_obj;
lean_object* v_a_2055_ = stack[5].m_obj;
lean_object* v_a_2056_ = stack[6].m_obj;
lean_object* v_a_2057_ = stack[7].m_obj;
lean_object* v_res_2072_;
v_res_2072_ = l_Lean_Expr_checkMaxShared(v_e_2050_, v_msg_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
stack->m_obj
 = v_res_2072_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___boxed(lean_object* v_e_2073_, lean_object* v_msg_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_Expr_checkMaxShared(v_e_2073_, v_msg_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(lean_object* v_00_u03b2_2083_, lean_object* v_x_2084_, lean_object* v_x_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_2084_, v_x_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___boxed(lean_object* v_00_u03b2_2087_, lean_object* v_x_2088_, lean_object* v_x_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(v_00_u03b2_2087_, v_x_2088_, v_x_2089_);
lean_dec_ref(v_x_2089_);
lean_dec_ref(v_x_2088_);
return v_res_2090_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_object* v_00_u03b2_2091_, lean_object* v_x_2092_, size_t v_x_2093_, lean_object* v_x_2094_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_2092_, v_x_2093_, v_x_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2092_ = stack[1].m_obj;
size_t v_x_2093_ = stack[2].m_num;
lean_object* v_x_2094_ = stack[3].m_obj;
lean_object* v_res_2096_;
v_res_2096_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_box(0), v_x_2092_, v_x_2093_, v_x_2094_);
stack->m_obj
 = v_res_2096_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2097_, lean_object* v_x_2098_, lean_object* v_x_2099_, lean_object* v_x_2100_){
_start:
{
size_t v_x_8274__boxed_2101_; lean_object* v_res_2102_; 
v_x_8274__boxed_2101_ = lean_unbox_usize(v_x_2099_);
lean_dec(v_x_2099_);
v_res_2102_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(v_00_u03b2_2097_, v_x_2098_, v_x_8274__boxed_2101_, v_x_2100_);
lean_dec_ref(v_x_2100_);
lean_dec_ref(v_x_2098_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(lean_object* v_00_u03b2_2103_, lean_object* v_m_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_2104_, v_a_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2107_, lean_object* v_m_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(v_00_u03b2_2107_, v_m_2108_, v_a_2109_);
lean_dec_ref(v_a_2109_);
lean_dec_ref(v_m_2108_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(lean_object* v_00_u03b2_2111_, lean_object* v_m_2112_, lean_object* v_a_2113_, lean_object* v_b_2114_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_m_2112_, v_a_2113_, v_b_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2116_, lean_object* v_keys_2117_, lean_object* v_vals_2118_, lean_object* v_heq_2119_, lean_object* v_i_2120_, lean_object* v_k_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_2117_, v_vals_2118_, v_i_2120_, v_k_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2123_, lean_object* v_keys_2124_, lean_object* v_vals_2125_, lean_object* v_heq_2126_, lean_object* v_i_2127_, lean_object* v_k_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(v_00_u03b2_2123_, v_keys_2124_, v_vals_2125_, v_heq_2126_, v_i_2127_, v_k_2128_);
lean_dec_ref(v_k_2128_);
lean_dec_ref(v_vals_2125_);
lean_dec_ref(v_keys_2124_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2130_, lean_object* v_a_2131_, lean_object* v_x_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_2131_, v_x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2134_, lean_object* v_a_2135_, lean_object* v_x_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(v_00_u03b2_2134_, v_a_2135_, v_x_2136_);
lean_dec(v_x_2136_);
lean_dec_ref(v_a_2135_);
return v_res_2137_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2138_, lean_object* v_a_2139_, lean_object* v_x_2140_){
_start:
{
uint8_t v___x_2141_; 
v___x_2141_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_2139_, v_x_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2139_ = stack[1].m_obj;
lean_object* v_x_2140_ = stack[2].m_obj;
uint8_t v_res_2142_;
v_res_2142_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_box(0), v_a_2139_, v_x_2140_);
stack->m_num = v_res_2142_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2143_, lean_object* v_a_2144_, lean_object* v_x_2145_){
_start:
{
uint8_t v_res_2146_; lean_object* v_r_2147_; 
v_res_2146_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(v_00_u03b2_2143_, v_a_2144_, v_x_2145_);
lean_dec(v_x_2145_);
lean_dec_ref(v_a_2144_);
v_r_2147_ = lean_box(v_res_2146_);
return v_r_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2148_, lean_object* v_data_2149_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_data_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2151_, lean_object* v_a_2152_, lean_object* v_b_2153_, lean_object* v_x_2154_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_2152_, v_b_2153_, v_x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_2156_, lean_object* v_i_2157_, lean_object* v_source_2158_, lean_object* v_target_2159_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v_i_2157_, v_source_2158_, v_target_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9(lean_object* v_00_u03b2_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_x_2162_, v_x_2163_);
return v___x_2164_;
}
}
lean_object* l_Lean_MVarId_checkMaxShared(lean_object* v_mvarId_2165_, lean_object* v_msg_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_MVarId_getDecl(v_mvarId_2165_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v_type_2176_; lean_object* v___x_2177_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
v_type_2176_ = lean_ctor_get(v_a_2175_, 2);
lean_inc_ref(v_type_2176_);
lean_dec(v_a_2175_);
v___x_2177_ = l_Lean_Expr_checkMaxShared(v_type_2176_, v_msg_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2177_;
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec_ref(v_msg_2166_);
v_a_2178_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2174_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2174_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_checkMaxShared_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2165_ = stack[0].m_obj;
lean_object* v_msg_2166_ = stack[1].m_obj;
lean_object* v_a_2167_ = stack[2].m_obj;
lean_object* v_a_2168_ = stack[3].m_obj;
lean_object* v_a_2169_ = stack[4].m_obj;
lean_object* v_a_2170_ = stack[5].m_obj;
lean_object* v_a_2171_ = stack[6].m_obj;
lean_object* v_a_2172_ = stack[7].m_obj;
lean_object* v_res_2186_;
v_res_2186_ = l_Lean_MVarId_checkMaxShared(v_mvarId_2165_, v_msg_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
stack->m_obj
 = v_res_2186_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared___boxed(lean_object* v_mvarId_2187_, lean_object* v_msg_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_MVarId_checkMaxShared(v_mvarId_2187_, v_msg_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
return v_res_2196_;
}
}
uint8_t l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(lean_object* v_x_2197_){
_start:
{
if (lean_obj_tag(v_x_2197_) == 0)
{
uint8_t v___x_2198_; 
v___x_2198_ = 0;
return v___x_2198_;
}
else
{
lean_object* v_head_2199_; lean_object* v_tail_2200_; uint8_t v___x_2201_; 
v_head_2199_ = lean_ctor_get(v_x_2197_, 0);
v_tail_2200_ = lean_ctor_get(v_x_2197_, 1);
v___x_2201_ = l_Lean_Level_isAlreadyNormalizedCheap(v_head_2199_);
if (v___x_2201_ == 0)
{
uint8_t v___x_2202_; 
v___x_2202_ = 1;
return v___x_2202_;
}
else
{
v_x_2197_ = v_tail_2200_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2197_ = stack[0].m_obj;
uint8_t v_res_2204_;
v_res_2204_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_x_2197_);
stack->m_num = v_res_2204_;
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0___boxed(lean_object* v_x_2205_){
_start:
{
uint8_t v_res_2206_; lean_object* v_r_2207_; 
v_res_2206_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_x_2205_);
lean_dec(v_x_2205_);
v_r_2207_ = lean_box(v_res_2206_);
return v_r_2207_;
}
}
uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(lean_object* v_x_2208_){
_start:
{
switch(lean_obj_tag(v_x_2208_))
{
case 4:
{
lean_object* v_us_2209_; uint8_t v___x_2210_; 
v_us_2209_ = lean_ctor_get(v_x_2208_, 1);
v___x_2210_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_us_2209_);
return v___x_2210_;
}
case 3:
{
lean_object* v_u_2211_; uint8_t v___x_2212_; 
v_u_2211_ = lean_ctor_get(v_x_2208_, 0);
v___x_2212_ = l_Lean_Level_isAlreadyNormalizedCheap(v_u_2211_);
if (v___x_2212_ == 0)
{
uint8_t v___x_2213_; 
v___x_2213_ = 1;
return v___x_2213_;
}
else
{
uint8_t v___x_2214_; 
v___x_2214_ = 0;
return v___x_2214_;
}
}
default: 
{
uint8_t v___x_2215_; 
v___x_2215_ = 0;
return v___x_2215_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2208_ = stack[0].m_obj;
uint8_t v_res_2216_;
v_res_2216_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(v_x_2208_);
stack->m_num = v_res_2216_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(lean_object* v_x_2217_){
_start:
{
uint8_t v_res_2218_; lean_object* v_r_2219_; 
v_res_2218_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(v_x_2217_);
lean_dec_ref(v_x_2217_);
v_r_2219_ = lean_box(v_res_2218_);
return v_r_2219_;
}
}
uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(lean_object* v_e_2221_){
_start:
{
lean_object* v___f_2222_; lean_object* v___x_2223_; 
v___f_2222_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0));
v___x_2223_ = lean_find_expr(v___f_2222_, v_e_2221_);
if (lean_obj_tag(v___x_2223_) == 0)
{
uint8_t v___x_2224_; 
v___x_2224_ = 1;
return v___x_2224_;
}
else
{
uint8_t v___x_2225_; 
lean_dec_ref_known(v___x_2223_, 1);
v___x_2225_ = 0;
return v___x_2225_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2221_ = stack[0].m_obj;
uint8_t v_res_2226_;
v_res_2226_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_2221_);
stack->m_num = v_res_2226_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___boxed(lean_object* v_e_2227_){
_start:
{
uint8_t v_res_2228_; lean_object* v_r_2229_; 
v_res_2228_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_2227_);
lean_dec_ref(v_e_2227_);
v_r_2229_ = lean_box(v_res_2228_);
return v_r_2229_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
if (lean_obj_tag(v_a_2230_) == 0)
{
lean_object* v___x_2232_; 
v___x_2232_ = l_List_reverse___redArg(v_a_2231_);
return v___x_2232_;
}
else
{
lean_object* v_head_2233_; lean_object* v_tail_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2243_; 
v_head_2233_ = lean_ctor_get(v_a_2230_, 0);
v_tail_2234_ = lean_ctor_get(v_a_2230_, 1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_a_2230_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2236_ = v_a_2230_;
v_isShared_2237_ = v_isSharedCheck_2243_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_tail_2234_);
lean_inc(v_head_2233_);
lean_dec(v_a_2230_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2243_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2238_ = l_Lean_Level_normalize(v_head_2233_);
lean_dec(v_head_2233_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 1, v_a_2231_);
lean_ctor_set(v___x_2236_, 0, v___x_2238_);
v___x_2240_ = v___x_2236_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2238_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_a_2231_);
v___x_2240_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
v_a_2230_ = v_tail_2234_;
v_a_2231_ = v___x_2240_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0(lean_object* v_e_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___y_2251_; lean_object* v___y_2255_; 
switch(lean_obj_tag(v_e_2246_))
{
case 3:
{
lean_object* v_u_2258_; lean_object* v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; uint8_t v___x_2262_; 
v_u_2258_ = lean_ctor_get(v_e_2246_, 0);
v___x_2259_ = l_Lean_Level_normalize(v_u_2258_);
v___x_2260_ = lean_ptr_addr(v_u_2258_);
v___x_2261_ = lean_ptr_addr(v___x_2259_);
v___x_2262_ = lean_usize_dec_eq(v___x_2260_, v___x_2261_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; 
lean_dec_ref_known(v_e_2246_, 1);
v___x_2263_ = l_Lean_Expr_sort___override(v___x_2259_);
v___y_2251_ = v___x_2263_;
goto v___jp_2250_;
}
else
{
lean_dec(v___x_2259_);
v___y_2251_ = v_e_2246_;
goto v___jp_2250_;
}
}
case 4:
{
lean_object* v_declName_2264_; lean_object* v_us_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v_declName_2264_ = lean_ctor_get(v_e_2246_, 0);
v_us_2265_ = lean_ctor_get(v_e_2246_, 1);
v___x_2266_ = lean_box(0);
lean_inc(v_us_2265_);
v___x_2267_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(v_us_2265_, v___x_2266_);
v___x_2268_ = l_ptrEqList___redArg(v_us_2265_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; 
lean_inc(v_declName_2264_);
lean_dec_ref_known(v_e_2246_, 2);
v___x_2269_ = l_Lean_Expr_const___override(v_declName_2264_, v___x_2267_);
v___y_2255_ = v___x_2269_;
goto v___jp_2254_;
}
else
{
lean_dec(v___x_2267_);
v___y_2255_ = v_e_2246_;
goto v___jp_2254_;
}
}
default: 
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec_ref(v_e_2246_);
v___x_2270_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___lam__0___closed__0));
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
return v___x_2271_;
}
}
v___jp_2250_:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___y_2251_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
v___jp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___y_2255_);
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
return v___x_2257_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_normalizeLevels___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2246_ = stack[0].m_obj;
lean_object* v___y_2247_ = stack[1].m_obj;
lean_object* v___y_2248_ = stack[2].m_obj;
lean_object* v_res_2272_;
v_res_2272_ = l_Lean_Meta_Sym_normalizeLevels___lam__0(v_e_2246_, v___y_2247_, v___y_2248_);
stack->m_obj
 = v_res_2272_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed(lean_object* v_e_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_Meta_Sym_normalizeLevels___lam__0(v_e_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
return v_res_2277_;
}
}
lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1(lean_object* v_e_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v_e_2278_);
v___x_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_normalizeLevels___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2278_ = stack[0].m_obj;
lean_object* v___y_2279_ = stack[1].m_obj;
lean_object* v___y_2280_ = stack[2].m_obj;
lean_object* v_res_2284_;
v_res_2284_ = l_Lean_Meta_Sym_normalizeLevels___lam__1(v_e_2278_, v___y_2279_, v___y_2280_);
stack->m_obj
 = v_res_2284_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed(lean_object* v_e_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_Meta_Sym_normalizeLevels___lam__1(v_e_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
return v_res_2289_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = l_Lean_maxRecDepthErrorMessage;
v___x_2296_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__3);
v___x_2298_ = l_Lean_MessageData_ofFormat(v___x_2297_);
return v___x_2298_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__4);
v___x_2300_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__2));
v___x_2301_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v___x_2299_);
return v___x_2301_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_ref_2302_){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___closed__5);
v___x_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2305_, 0, v_ref_2302_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2302_ = stack[0].m_obj;
lean_object* v_res_2307_;
v_res_2307_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2302_);
stack->m_obj
 = v_res_2307_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_ref_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2308_);
return v_res_2310_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2311_ = lean_box(0);
v___x_2312_ = l_Lean_interruptExceptionId;
v___x_2313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
lean_ctor_set(v___x_2313_, 1, v___x_2311_);
return v___x_2313_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg(){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___closed__0);
v___x_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2317_;
v_res_2317_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
stack->m_obj
 = v_res_2317_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg___boxed(lean_object* v___y_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
return v_res_2319_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(lean_object* v_x_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___y_2326_; lean_object* v___y_2336_; lean_object* v___y_2337_; uint8_t v___y_2338_; uint8_t v___y_2339_; uint16_t v___y_2340_; lean_object* v___y_2341_; lean_object* v_toCold_2346_; lean_object* v_currRecDepth_2347_; lean_object* v_ref_2348_; uint16_t v_optionFlags_2349_; uint8_t v_suppressElabErrors_2350_; uint8_t v_isRecordingDeps_2351_; lean_object* v_maxRecDepth_2352_; lean_object* v_cancelTk_x3f_2353_; 
v_toCold_2346_ = lean_ctor_get(v___y_2322_, 0);
v_currRecDepth_2347_ = lean_ctor_get(v___y_2322_, 1);
v_ref_2348_ = lean_ctor_get(v___y_2322_, 2);
v_optionFlags_2349_ = lean_ctor_get_uint16(v___y_2322_, sizeof(void*)*3);
v_suppressElabErrors_2350_ = lean_ctor_get_uint8(v___y_2322_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2351_ = lean_ctor_get_uint8(v___y_2322_, sizeof(void*)*3 + 3);
v_maxRecDepth_2352_ = lean_ctor_get(v_toCold_2346_, 3);
v_cancelTk_x3f_2353_ = lean_ctor_get(v_toCold_2346_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2353_) == 1)
{
lean_object* v_val_2359_; uint8_t v___x_2360_; 
v_val_2359_ = lean_ctor_get(v_cancelTk_x3f_2353_, 0);
v___x_2360_ = l_IO_CancelToken_isSet(v_val_2359_);
if (v___x_2360_ == 0)
{
goto v___jp_2354_;
}
else
{
lean_object* v___x_2361_; lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec_ref(v_x_2320_);
v___x_2361_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
goto v___jp_2354_;
}
v___jp_2325_:
{
if (lean_obj_tag(v___y_2326_) == 0)
{
return v___y_2326_;
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
v_a_2327_ = lean_ctor_get(v___y_2326_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___y_2326_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___y_2326_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___y_2326_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
v___jp_2335_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2342_ = lean_unsigned_to_nat(1u);
v___x_2343_ = lean_nat_add(v___y_2337_, v___x_2342_);
lean_inc_ref(v___y_2341_);
v___x_2344_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2344_, 0, v___y_2341_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
lean_ctor_set(v___x_2344_, 2, v___y_2336_);
lean_ctor_set_uint16(v___x_2344_, sizeof(void*)*3, v___y_2340_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*3 + 2, v___y_2339_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*3 + 3, v___y_2338_);
lean_inc(v___y_2323_);
lean_inc(v___y_2321_);
v___x_2345_ = lean_apply_4(v_x_2320_, v___y_2321_, v___x_2344_, v___y_2323_, lean_box(0));
v___y_2326_ = v___x_2345_;
goto v___jp_2325_;
}
v___jp_2354_:
{
lean_object* v___x_2355_; uint8_t v___x_2356_; 
v___x_2355_ = lean_unsigned_to_nat(0u);
v___x_2356_ = lean_nat_dec_eq(v_maxRecDepth_2352_, v___x_2355_);
if (v___x_2356_ == 0)
{
uint8_t v___x_2357_; 
v___x_2357_ = lean_nat_dec_eq(v_currRecDepth_2347_, v_maxRecDepth_2352_);
if (v___x_2357_ == 0)
{
lean_inc(v_ref_2348_);
v___y_2336_ = v_ref_2348_;
v___y_2337_ = v_currRecDepth_2347_;
v___y_2338_ = v_isRecordingDeps_2351_;
v___y_2339_ = v_suppressElabErrors_2350_;
v___y_2340_ = v_optionFlags_2349_;
v___y_2341_ = v_toCold_2346_;
goto v___jp_2335_;
}
else
{
lean_object* v___x_2358_; 
lean_dec_ref(v_x_2320_);
lean_inc(v_ref_2348_);
v___x_2358_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2348_);
v___y_2326_ = v___x_2358_;
goto v___jp_2325_;
}
}
else
{
lean_inc(v_ref_2348_);
v___y_2336_ = v_ref_2348_;
v___y_2337_ = v_currRecDepth_2347_;
v___y_2338_ = v_isRecordingDeps_2351_;
v___y_2339_ = v_suppressElabErrors_2350_;
v___y_2340_ = v_optionFlags_2349_;
v___y_2341_ = v_toCold_2346_;
goto v___jp_2335_;
}
}
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2320_ = stack[0].m_obj;
lean_object* v___y_2321_ = stack[1].m_obj;
lean_object* v___y_2322_ = stack[2].m_obj;
lean_object* v___y_2323_ = stack[3].m_obj;
lean_object* v_res_2370_;
v_res_2370_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v_x_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
stack->m_obj
 = v_res_2370_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_x_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v_x_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(lean_object* v_x_2377_, lean_object* v_x_2378_){
_start:
{
if (lean_obj_tag(v_x_2378_) == 0)
{
return v_x_2377_;
}
else
{
lean_object* v_key_2379_; lean_object* v_value_2380_; lean_object* v_tail_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2404_; 
v_key_2379_ = lean_ctor_get(v_x_2378_, 0);
v_value_2380_ = lean_ctor_get(v_x_2378_, 1);
v_tail_2381_ = lean_ctor_get(v_x_2378_, 2);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_x_2378_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2383_ = v_x_2378_;
v_isShared_2384_ = v_isSharedCheck_2404_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_tail_2381_);
lean_inc(v_value_2380_);
lean_inc(v_key_2379_);
lean_dec(v_x_2378_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2404_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; uint64_t v___x_2386_; uint64_t v___x_2387_; uint64_t v___x_2388_; uint64_t v_fold_2389_; uint64_t v___x_2390_; uint64_t v___x_2391_; uint64_t v___x_2392_; size_t v___x_2393_; size_t v___x_2394_; size_t v___x_2395_; size_t v___x_2396_; size_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2385_ = lean_array_get_size(v_x_2377_);
v___x_2386_ = l_Lean_ExprStructEq_hash(v_key_2379_);
v___x_2387_ = 32ULL;
v___x_2388_ = lean_uint64_shift_right(v___x_2386_, v___x_2387_);
v_fold_2389_ = lean_uint64_xor(v___x_2386_, v___x_2388_);
v___x_2390_ = 16ULL;
v___x_2391_ = lean_uint64_shift_right(v_fold_2389_, v___x_2390_);
v___x_2392_ = lean_uint64_xor(v_fold_2389_, v___x_2391_);
v___x_2393_ = lean_uint64_to_usize(v___x_2392_);
v___x_2394_ = lean_usize_of_nat(v___x_2385_);
v___x_2395_ = ((size_t)1ULL);
v___x_2396_ = lean_usize_sub(v___x_2394_, v___x_2395_);
v___x_2397_ = lean_usize_land(v___x_2393_, v___x_2396_);
v___x_2398_ = lean_array_uget_borrowed(v_x_2377_, v___x_2397_);
lean_inc(v___x_2398_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 2, v___x_2398_);
v___x_2400_ = v___x_2383_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_key_2379_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_value_2380_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_array_uset(v_x_2377_, v___x_2397_, v___x_2400_);
v_x_2377_ = v___x_2401_;
v_x_2378_ = v_tail_2381_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(lean_object* v_i_2405_, lean_object* v_source_2406_, lean_object* v_target_2407_){
_start:
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = lean_array_get_size(v_source_2406_);
v___x_2409_ = lean_nat_dec_lt(v_i_2405_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_dec_ref(v_source_2406_);
lean_dec(v_i_2405_);
return v_target_2407_;
}
else
{
lean_object* v_es_2410_; lean_object* v___x_2411_; lean_object* v_source_2412_; lean_object* v_target_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_es_2410_ = lean_array_fget(v_source_2406_, v_i_2405_);
v___x_2411_ = lean_box(0);
v_source_2412_ = lean_array_fset(v_source_2406_, v_i_2405_, v___x_2411_);
v_target_2413_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_target_2407_, v_es_2410_);
v___x_2414_ = lean_unsigned_to_nat(1u);
v___x_2415_ = lean_nat_add(v_i_2405_, v___x_2414_);
lean_dec(v_i_2405_);
v_i_2405_ = v___x_2415_;
v_source_2406_ = v_source_2412_;
v_target_2407_ = v_target_2413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12___redArg(lean_object* v_data_2417_){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v_nbuckets_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2418_ = lean_array_get_size(v_data_2417_);
v___x_2419_ = lean_unsigned_to_nat(2u);
v_nbuckets_2420_ = lean_nat_mul(v___x_2418_, v___x_2419_);
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = lean_box(0);
v___x_2423_ = lean_mk_array(v_nbuckets_2420_, v___x_2422_);
v___x_2424_ = lean_array_propagate_mark(v_data_2417_, v___x_2423_);
v___x_2425_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v___x_2421_, v_data_2417_, v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(lean_object* v_a_2426_, lean_object* v_b_2427_, lean_object* v_x_2428_){
_start:
{
if (lean_obj_tag(v_x_2428_) == 0)
{
lean_dec(v_b_2427_);
lean_dec_ref(v_a_2426_);
return v_x_2428_;
}
else
{
lean_object* v_key_2429_; lean_object* v_value_2430_; lean_object* v_tail_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2443_; 
v_key_2429_ = lean_ctor_get(v_x_2428_, 0);
v_value_2430_ = lean_ctor_get(v_x_2428_, 1);
v_tail_2431_ = lean_ctor_get(v_x_2428_, 2);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_x_2428_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2433_ = v_x_2428_;
v_isShared_2434_ = v_isSharedCheck_2443_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_tail_2431_);
lean_inc(v_value_2430_);
lean_inc(v_key_2429_);
lean_dec(v_x_2428_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2443_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
uint8_t v___x_2435_; 
v___x_2435_ = l_Lean_ExprStructEq_beq(v_key_2429_, v_a_2426_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2436_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(v_a_2426_, v_b_2427_, v_tail_2431_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 2, v___x_2436_);
v___x_2438_ = v___x_2433_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_key_2429_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_value_2430_);
lean_ctor_set(v_reuseFailAlloc_2439_, 2, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
else
{
lean_object* v___x_2441_; 
lean_dec(v_value_2430_);
lean_dec(v_key_2429_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 1, v_b_2427_);
lean_ctor_set(v___x_2433_, 0, v_a_2426_);
v___x_2441_ = v___x_2433_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2426_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_b_2427_);
lean_ctor_set(v_reuseFailAlloc_2442_, 2, v_tail_2431_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_a_2444_, lean_object* v_x_2445_){
_start:
{
if (lean_obj_tag(v_x_2445_) == 0)
{
uint8_t v___x_2446_; 
v___x_2446_ = 0;
return v___x_2446_;
}
else
{
lean_object* v_key_2447_; lean_object* v_tail_2448_; uint8_t v___x_2449_; 
v_key_2447_ = lean_ctor_get(v_x_2445_, 0);
v_tail_2448_ = lean_ctor_get(v_x_2445_, 2);
v___x_2449_ = l_Lean_ExprStructEq_beq(v_key_2447_, v_a_2444_);
if (v___x_2449_ == 0)
{
v_x_2445_ = v_tail_2448_;
goto _start;
}
else
{
return v___x_2449_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2444_ = stack[0].m_obj;
lean_object* v_x_2445_ = stack[1].m_obj;
uint8_t v_res_2451_;
v_res_2451_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_a_2444_, v_x_2445_);
stack->m_num = v_res_2451_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object* v_a_2452_, lean_object* v_x_2453_){
_start:
{
uint8_t v_res_2454_; lean_object* v_r_2455_; 
v_res_2454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_a_2452_, v_x_2453_);
lean_dec(v_x_2453_);
lean_dec_ref(v_a_2452_);
v_r_2455_ = lean_box(v_res_2454_);
return v_r_2455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(lean_object* v_m_2456_, lean_object* v_a_2457_, lean_object* v_b_2458_){
_start:
{
lean_object* v_size_2459_; lean_object* v_buckets_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2503_; 
v_size_2459_ = lean_ctor_get(v_m_2456_, 0);
v_buckets_2460_ = lean_ctor_get(v_m_2456_, 1);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_m_2456_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2462_ = v_m_2456_;
v_isShared_2463_ = v_isSharedCheck_2503_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_buckets_2460_);
lean_inc(v_size_2459_);
lean_dec(v_m_2456_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2503_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; uint64_t v___x_2465_; uint64_t v___x_2466_; uint64_t v___x_2467_; uint64_t v_fold_2468_; uint64_t v___x_2469_; uint64_t v___x_2470_; uint64_t v___x_2471_; size_t v___x_2472_; size_t v___x_2473_; size_t v___x_2474_; size_t v___x_2475_; size_t v___x_2476_; lean_object* v_bkt_2477_; uint8_t v___x_2478_; 
v___x_2464_ = lean_array_get_size(v_buckets_2460_);
v___x_2465_ = l_Lean_ExprStructEq_hash(v_a_2457_);
v___x_2466_ = 32ULL;
v___x_2467_ = lean_uint64_shift_right(v___x_2465_, v___x_2466_);
v_fold_2468_ = lean_uint64_xor(v___x_2465_, v___x_2467_);
v___x_2469_ = 16ULL;
v___x_2470_ = lean_uint64_shift_right(v_fold_2468_, v___x_2469_);
v___x_2471_ = lean_uint64_xor(v_fold_2468_, v___x_2470_);
v___x_2472_ = lean_uint64_to_usize(v___x_2471_);
v___x_2473_ = lean_usize_of_nat(v___x_2464_);
v___x_2474_ = ((size_t)1ULL);
v___x_2475_ = lean_usize_sub(v___x_2473_, v___x_2474_);
v___x_2476_ = lean_usize_land(v___x_2472_, v___x_2475_);
v_bkt_2477_ = lean_array_uget_borrowed(v_buckets_2460_, v___x_2476_);
v___x_2478_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_a_2457_, v_bkt_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v_size_x27_2480_; lean_object* v___x_2481_; lean_object* v_buckets_x27_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2479_ = lean_unsigned_to_nat(1u);
v_size_x27_2480_ = lean_nat_add(v_size_2459_, v___x_2479_);
lean_dec(v_size_2459_);
lean_inc(v_bkt_2477_);
v___x_2481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2481_, 0, v_a_2457_);
lean_ctor_set(v___x_2481_, 1, v_b_2458_);
lean_ctor_set(v___x_2481_, 2, v_bkt_2477_);
v_buckets_x27_2482_ = lean_array_uset(v_buckets_2460_, v___x_2476_, v___x_2481_);
v___x_2483_ = lean_unsigned_to_nat(4u);
v___x_2484_ = lean_nat_mul(v_size_x27_2480_, v___x_2483_);
v___x_2485_ = lean_unsigned_to_nat(3u);
v___x_2486_ = lean_nat_div(v___x_2484_, v___x_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_array_get_size(v_buckets_x27_2482_);
v___x_2488_ = lean_nat_dec_le(v___x_2486_, v___x_2487_);
lean_dec(v___x_2486_);
if (v___x_2488_ == 0)
{
lean_object* v_val_2489_; lean_object* v___x_2491_; 
v_val_2489_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12___redArg(v_buckets_x27_2482_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v_val_2489_);
lean_ctor_set(v___x_2462_, 0, v_size_x27_2480_);
v___x_2491_ = v___x_2462_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_size_x27_2480_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_val_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
else
{
lean_object* v___x_2494_; 
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v_buckets_x27_2482_);
lean_ctor_set(v___x_2462_, 0, v_size_x27_2480_);
v___x_2494_ = v___x_2462_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_size_x27_2480_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v_buckets_x27_2482_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
else
{
lean_object* v___x_2496_; lean_object* v_buckets_x27_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
lean_inc(v_bkt_2477_);
v___x_2496_ = lean_box(0);
v_buckets_x27_2497_ = lean_array_uset(v_buckets_2460_, v___x_2476_, v___x_2496_);
v___x_2498_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(v_a_2457_, v_b_2458_, v_bkt_2477_);
v___x_2499_ = lean_array_uset(v_buckets_x27_2497_, v___x_2476_, v___x_2498_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v___x_2499_);
v___x_2501_ = v___x_2462_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_size_2459_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2(lean_object* v_a_2504_, lean_object* v_e_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2508_ = lean_st_ref_take(v_a_2504_);
v___x_2509_ = lean_box(0);
v___x_2510_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v___x_2508_, v_e_2505_, v_a_2506_);
v___x_2511_ = lean_st_ref_put(v_a_2504_, v___x_2510_);
return v___x_2509_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2504_ = stack[0].m_obj;
lean_object* v_e_2505_ = stack[1].m_obj;
lean_object* v_a_2506_ = stack[2].m_obj;
lean_object* v_res_2512_;
v_res_2512_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2(v_a_2504_, v_e_2505_, v_a_2506_);
stack->m_obj
 = v_res_2512_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2513_, lean_object* v_e_2514_, lean_object* v_a_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2(v_a_2513_, v_e_2514_, v_a_2515_);
lean_dec(v_a_2513_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_a_2518_, lean_object* v_x_2519_){
_start:
{
if (lean_obj_tag(v_x_2519_) == 0)
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_box(0);
return v___x_2520_;
}
else
{
lean_object* v_key_2521_; lean_object* v_value_2522_; lean_object* v_tail_2523_; uint8_t v___x_2524_; 
v_key_2521_ = lean_ctor_get(v_x_2519_, 0);
v_value_2522_ = lean_ctor_get(v_x_2519_, 1);
v_tail_2523_ = lean_ctor_get(v_x_2519_, 2);
v___x_2524_ = l_Lean_ExprStructEq_beq(v_key_2521_, v_a_2518_);
if (v___x_2524_ == 0)
{
v_x_2519_ = v_tail_2523_;
goto _start;
}
else
{
lean_object* v___x_2526_; 
lean_inc(v_value_2522_);
v___x_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2526_, 0, v_value_2522_);
return v___x_2526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg___boxed(lean_object* v_a_2527_, lean_object* v_x_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(v_a_2527_, v_x_2528_);
lean_dec(v_x_2528_);
lean_dec_ref(v_a_2527_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(lean_object* v_m_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_buckets_2532_; lean_object* v___x_2533_; uint64_t v___x_2534_; uint64_t v___x_2535_; uint64_t v___x_2536_; uint64_t v_fold_2537_; uint64_t v___x_2538_; uint64_t v___x_2539_; uint64_t v___x_2540_; size_t v___x_2541_; size_t v___x_2542_; size_t v___x_2543_; size_t v___x_2544_; size_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v_buckets_2532_ = lean_ctor_get(v_m_2530_, 1);
v___x_2533_ = lean_array_get_size(v_buckets_2532_);
v___x_2534_ = l_Lean_ExprStructEq_hash(v_a_2531_);
v___x_2535_ = 32ULL;
v___x_2536_ = lean_uint64_shift_right(v___x_2534_, v___x_2535_);
v_fold_2537_ = lean_uint64_xor(v___x_2534_, v___x_2536_);
v___x_2538_ = 16ULL;
v___x_2539_ = lean_uint64_shift_right(v_fold_2537_, v___x_2538_);
v___x_2540_ = lean_uint64_xor(v_fold_2537_, v___x_2539_);
v___x_2541_ = lean_uint64_to_usize(v___x_2540_);
v___x_2542_ = lean_usize_of_nat(v___x_2533_);
v___x_2543_ = ((size_t)1ULL);
v___x_2544_ = lean_usize_sub(v___x_2542_, v___x_2543_);
v___x_2545_ = lean_usize_land(v___x_2541_, v___x_2544_);
v___x_2546_ = lean_array_uget_borrowed(v_buckets_2532_, v___x_2545_);
v___x_2547_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(v_a_2531_, v___x_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_m_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(v_m_2548_, v_a_2549_);
lean_dec_ref(v_a_2549_);
lean_dec_ref(v_m_2548_);
return v_res_2550_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2551_, lean_object* v_x_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = lean_apply_1(v_x_2552_, lean_box(0));
v___x_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2552_ = stack[1].m_obj;
lean_object* v___y_2553_ = stack[2].m_obj;
lean_object* v___y_2554_ = stack[3].m_obj;
lean_object* v_res_2558_;
v_res_2558_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v_x_2552_, v___y_2553_, v___y_2554_);
stack->m_obj
 = v_res_2558_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2559_, lean_object* v_x_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(v_00_u03b1_2559_, v_x_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
return v_res_2564_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2566_; lean_object* v_dummy_2567_; 
v___x_2566_ = lean_box(0);
v_dummy_2567_ = l_Lean_Expr_sort___override(v___x_2566_);
return v_dummy_2567_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object* v_pre_2568_, lean_object* v_post_2569_, size_t v_sz_2570_, size_t v_i_2571_, lean_object* v_bs_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
uint8_t v___x_2577_; 
v___x_2577_ = lean_usize_dec_lt(v_i_2571_, v_sz_2570_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; 
lean_dec_ref(v_post_2569_);
lean_dec_ref(v_pre_2568_);
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v_bs_2572_);
return v___x_2578_;
}
else
{
lean_object* v_v_2579_; lean_object* v___x_2580_; lean_object* v_bs_x27_2581_; lean_object* v___x_2582_; 
v_v_2579_ = lean_array_uget(v_bs_2572_, v_i_2571_);
v___x_2580_ = lean_unsigned_to_nat(0u);
v_bs_x27_2581_ = lean_array_uset(v_bs_2572_, v_i_2571_, v___x_2580_);
lean_inc_ref(v_post_2569_);
lean_inc_ref(v_pre_2568_);
v___x_2582_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2568_, v_post_2569_, v_v_2579_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; size_t v___x_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2584_ = ((size_t)1ULL);
v___x_2585_ = lean_usize_add(v_i_2571_, v___x_2584_);
v___x_2586_ = lean_array_uset(v_bs_x27_2581_, v_i_2571_, v_a_2583_);
v_i_2571_ = v___x_2585_;
v_bs_2572_ = v___x_2586_;
goto _start;
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v_bs_x27_2581_);
lean_dec_ref(v_post_2569_);
lean_dec_ref(v_pre_2568_);
v_a_2588_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2582_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2582_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2568_ = stack[0].m_obj;
lean_object* v_post_2569_ = stack[1].m_obj;
size_t v_sz_2570_ = stack[2].m_num;
size_t v_i_2571_ = stack[3].m_num;
lean_object* v_bs_2572_ = stack[4].m_obj;
lean_object* v___y_2573_ = stack[5].m_obj;
lean_object* v___y_2574_ = stack[6].m_obj;
lean_object* v___y_2575_ = stack[7].m_obj;
lean_object* v_res_2596_;
v_res_2596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_2568_, v_post_2569_, v_sz_2570_, v_i_2571_, v_bs_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
stack->m_obj
 = v_res_2596_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(lean_object* v_pre_2597_, lean_object* v_post_2598_, lean_object* v_x_2599_, lean_object* v_x_2600_, lean_object* v_x_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
if (lean_obj_tag(v_x_2599_) == 5)
{
lean_object* v_fn_2606_; lean_object* v_arg_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v_fn_2606_ = lean_ctor_get(v_x_2599_, 0);
lean_inc_ref(v_fn_2606_);
v_arg_2607_ = lean_ctor_get(v_x_2599_, 1);
lean_inc_ref(v_arg_2607_);
lean_dec_ref_known(v_x_2599_, 2);
v___x_2608_ = lean_array_set(v_x_2600_, v_x_2601_, v_arg_2607_);
v___x_2609_ = lean_unsigned_to_nat(1u);
v___x_2610_ = lean_nat_sub(v_x_2601_, v___x_2609_);
lean_dec(v_x_2601_);
v_x_2599_ = v_fn_2606_;
v_x_2600_ = v___x_2608_;
v_x_2601_ = v___x_2610_;
goto _start;
}
else
{
lean_object* v___x_2612_; 
lean_dec(v_x_2601_);
lean_inc_ref(v_post_2598_);
lean_inc_ref(v_pre_2597_);
v___x_2612_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2597_, v_post_2598_, v_x_2599_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; size_t v_sz_2614_; size_t v___x_2615_; lean_object* v___x_2616_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2612_, 1);
v_sz_2614_ = lean_array_size(v_x_2600_);
v___x_2615_ = ((size_t)0ULL);
lean_inc_ref(v_post_2598_);
lean_inc_ref(v_pre_2597_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_2597_, v_post_2598_, v_sz_2614_, v___x_2615_, v_x_2600_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = l_Lean_mkAppN(v_a_2613_, v_a_2617_);
lean_dec(v_a_2617_);
v___x_2619_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2597_, v_post_2598_, v___x_2618_, v___y_2602_, v___y_2603_, v___y_2604_);
return v___x_2619_;
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v_a_2613_);
lean_dec_ref(v_post_2598_);
lean_dec_ref(v_pre_2597_);
v_a_2620_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2616_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2616_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
else
{
lean_dec_ref(v_x_2600_);
lean_dec_ref(v_post_2598_);
lean_dec_ref(v_pre_2597_);
return v___x_2612_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2597_ = stack[0].m_obj;
lean_object* v_post_2598_ = stack[1].m_obj;
lean_object* v_x_2599_ = stack[2].m_obj;
lean_object* v_x_2600_ = stack[3].m_obj;
lean_object* v_x_2601_ = stack[4].m_obj;
lean_object* v___y_2602_ = stack[5].m_obj;
lean_object* v___y_2603_ = stack[6].m_obj;
lean_object* v___y_2604_ = stack[7].m_obj;
lean_object* v_res_2628_;
v_res_2628_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_pre_2597_, v_post_2598_, v_x_2599_, v_x_2600_, v_x_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
stack->m_obj
 = v_res_2628_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object* v___x_2629_, lean_object* v_pre_2630_, lean_object* v_e_2631_, lean_object* v_post_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_Core_checkSystem(v___x_2629_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v___x_2638_; 
lean_dec_ref_known(v___x_2637_, 1);
lean_inc_ref(v_pre_2630_);
lean_inc(v___y_2635_);
lean_inc_ref(v___y_2634_);
lean_inc_ref(v_e_2631_);
v___x_2638_ = lean_apply_4(v_pre_2630_, v_e_2631_, v___y_2634_, v___y_2635_, lean_box(0));
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2754_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2754_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2754_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___y_2644_; 
switch(lean_obj_tag(v_a_2639_))
{
case 0:
{
lean_object* v_e_2744_; lean_object* v___x_2746_; 
lean_dec_ref(v_post_2632_);
lean_dec_ref(v_e_2631_);
lean_dec_ref(v_pre_2630_);
v_e_2744_ = lean_ctor_get(v_a_2639_, 0);
lean_inc_ref(v_e_2744_);
lean_dec_ref_known(v_a_2639_, 1);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v_e_2744_);
v___x_2746_ = v___x_2641_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_e_2744_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
case 1:
{
lean_object* v_e_2748_; lean_object* v___x_2749_; 
lean_del_object(v___x_2641_);
lean_dec_ref(v_e_2631_);
v_e_2748_ = lean_ctor_get(v_a_2639_, 0);
lean_inc_ref(v_e_2748_);
lean_dec_ref_known(v_a_2639_, 1);
lean_inc_ref(v_post_2632_);
lean_inc_ref(v_pre_2630_);
v___x_2749_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2630_, v_post_2632_, v_e_2748_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2751_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v___x_2751_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v_a_2750_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2751_;
}
else
{
lean_dec_ref(v_post_2632_);
lean_dec_ref(v_pre_2630_);
return v___x_2749_;
}
}
default: 
{
lean_object* v_e_x3f_2752_; 
lean_del_object(v___x_2641_);
v_e_x3f_2752_ = lean_ctor_get(v_a_2639_, 0);
lean_inc(v_e_x3f_2752_);
lean_dec_ref_known(v_a_2639_, 1);
if (lean_obj_tag(v_e_x3f_2752_) == 0)
{
v___y_2644_ = v_e_2631_;
goto v___jp_2643_;
}
else
{
lean_object* v_val_2753_; 
lean_dec_ref(v_e_2631_);
v_val_2753_ = lean_ctor_get(v_e_x3f_2752_, 0);
lean_inc(v_val_2753_);
lean_dec_ref_known(v_e_x3f_2752_, 1);
v___y_2644_ = v_val_2753_;
goto v___jp_2643_;
}
}
}
v___jp_2643_:
{
switch(lean_obj_tag(v___y_2644_))
{
case 7:
{
lean_object* v_binderName_2645_; lean_object* v_binderType_2646_; lean_object* v_body_2647_; uint8_t v_binderInfo_2648_; lean_object* v___x_2649_; 
v_binderName_2645_ = lean_ctor_get(v___y_2644_, 0);
v_binderType_2646_ = lean_ctor_get(v___y_2644_, 1);
v_body_2647_ = lean_ctor_get(v___y_2644_, 2);
v_binderInfo_2648_ = lean_ctor_get_uint8(v___y_2644_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2646_);
lean_inc_ref(v_post_2632_);
lean_inc_ref(v_pre_2630_);
v___x_2649_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2630_, v_post_2632_, v_binderType_2646_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2651_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
lean_inc_ref(v_body_2647_);
lean_inc_ref(v_post_2632_);
lean_inc_ref(v_pre_2630_);
v___x_2651_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2630_, v_post_2632_, v_body_2647_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; size_t v___x_2653_; size_t v___x_2654_; uint8_t v___x_2655_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
v___x_2653_ = lean_ptr_addr(v_binderType_2646_);
v___x_2654_ = lean_ptr_addr(v_a_2650_);
v___x_2655_ = lean_usize_dec_eq(v___x_2653_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_inc(v_binderName_2645_);
lean_dec_ref_known(v___y_2644_, 3);
v___x_2656_ = l_Lean_Expr_forallE___override(v_binderName_2645_, v_a_2650_, v_a_2652_, v_binderInfo_2648_);
v___x_2657_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___x_2656_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2657_;
}
else
{
size_t v___x_2658_; size_t v___x_2659_; uint8_t v___x_2660_; 
v___x_2658_ = lean_ptr_addr(v_body_2647_);
v___x_2659_ = lean_ptr_addr(v_a_2652_);
v___x_2660_ = lean_usize_dec_eq(v___x_2658_, v___x_2659_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_inc(v_binderName_2645_);
lean_dec_ref_known(v___y_2644_, 3);
v___x_2661_ = l_Lean_Expr_forallE___override(v_binderName_2645_, v_a_2650_, v_a_2652_, v_binderInfo_2648_);
v___x_2662_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___x_2661_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2662_;
}
else
{
uint8_t v___x_2663_; 
v___x_2663_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2648_, v_binderInfo_2648_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_inc(v_binderName_2645_);
lean_dec_ref_known(v___y_2644_, 3);
v___x_2664_ = l_Lean_Expr_forallE___override(v_binderName_2645_, v_a_2650_, v_a_2652_, v_binderInfo_2648_);
v___x_2665_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___x_2664_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2665_;
}
else
{
lean_object* v___x_2666_; 
lean_dec(v_a_2652_);
lean_dec(v_a_2650_);
v___x_2666_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___y_2644_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2666_;
}
}
}
}
else
{
lean_dec(v_a_2650_);
lean_dec_ref_known(v___y_2644_, 3);
lean_dec_ref(v_post_2632_);
lean_dec_ref(v_pre_2630_);
return v___x_2651_;
}
}
else
{
lean_dec_ref_known(v___y_2644_, 3);
lean_dec_ref(v_post_2632_);
lean_dec_ref(v_pre_2630_);
return v___x_2649_;
}
}
case 6:
{
lean_object* v_binderName_2667_; lean_object* v_binderType_2668_; lean_object* v_body_2669_; uint8_t v_binderInfo_2670_; lean_object* v___x_2671_; 
v_binderName_2667_ = lean_ctor_get(v___y_2644_, 0);
v_binderType_2668_ = lean_ctor_get(v___y_2644_, 1);
v_body_2669_ = lean_ctor_get(v___y_2644_, 2);
v_binderInfo_2670_ = lean_ctor_get_uint8(v___y_2644_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2668_);
lean_inc_ref(v_post_2632_);
lean_inc_ref(v_pre_2630_);
v___x_2671_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2630_, v_post_2632_, v_binderType_2668_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2673_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
lean_inc_ref(v_body_2669_);
lean_inc_ref(v_post_2632_);
lean_inc_ref(v_pre_2630_);
v___x_2673_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2630_, v_post_2632_, v_body_2669_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; size_t v___x_2675_; size_t v___x_2676_; uint8_t v___x_2677_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2675_ = lean_ptr_addr(v_binderType_2668_);
v___x_2676_ = lean_ptr_addr(v_a_2672_);
v___x_2677_ = lean_usize_dec_eq(v___x_2675_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_inc(v_binderName_2667_);
lean_dec_ref_known(v___y_2644_, 3);
v___x_2678_ = l_Lean_Expr_lam___override(v_binderName_2667_, v_a_2672_, v_a_2674_, v_binderInfo_2670_);
v___x_2679_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___x_2678_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2679_;
}
else
{
size_t v___x_2680_; size_t v___x_2681_; uint8_t v___x_2682_; 
v___x_2680_ = lean_ptr_addr(v_body_2669_);
v___x_2681_ = lean_ptr_addr(v_a_2674_);
v___x_2682_ = lean_usize_dec_eq(v___x_2680_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
lean_inc(v_binderName_2667_);
lean_dec_ref_known(v___y_2644_, 3);
v___x_2683_ = l_Lean_Expr_lam___override(v_binderName_2667_, v_a_2672_, v_a_2674_, v_binderInfo_2670_);
v___x_2684_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___x_2683_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2684_;
}
else
{
uint8_t v___x_2685_; 
v___x_2685_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2670_, v_binderInfo_2670_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_inc(v_binderName_2667_);
lean_dec_ref_known(v___y_2644_, 3);
v___x_2686_ = l_Lean_Expr_lam___override(v_binderName_2667_, v_a_2672_, v_a_2674_, v_binderInfo_2670_);
v___x_2687_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___x_2686_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2687_;
}
else
{
lean_object* v___x_2688_; 
lean_dec(v_a_2674_);
lean_dec(v_a_2672_);
v___x_2688_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___y_2644_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2688_;
}
}
}
}
else
{
lean_dec(v_a_2672_);
lean_dec_ref_known(v___y_2644_, 3);
lean_dec_ref(v_post_2632_);
lean_dec_ref(v_pre_2630_);
return v___x_2673_;
}
}
else
{
lean_dec_ref_known(v___y_2644_, 3);
lean_dec_ref(v_post_2632_);
lean_dec_ref(v_pre_2630_);
return v___x_2671_;
}
}
case 8:
{
lean_object* v_declName_2689_; lean_object* v_type_2690_; lean_object* v_value_2691_; lean_object* v_body_2692_; uint8_t v_nondep_2693_; lean_object* v___x_2694_; 
v_declName_2689_ = lean_ctor_get(v___y_2644_, 0);
v_type_2690_ = lean_ctor_get(v___y_2644_, 1);
v_value_2691_ = lean_ctor_get(v___y_2644_, 2);
v_body_2692_ = lean_ctor_get(v___y_2644_, 3);
v_nondep_2693_ = lean_ctor_get_uint8(v___y_2644_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2690_);
lean_inc_ref(v_post_2632_);
lean_inc_ref(v_pre_2630_);
v___x_2694_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2630_, v_post_2632_, v_type_2690_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2696_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2694_, 1);
lean_inc_ref(v_value_2691_);
lean_inc_ref(v_post_2632_);
lean_inc_ref(v_pre_2630_);
v___x_2696_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2630_, v_post_2632_, v_value_2691_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2698_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref_known(v___x_2696_, 1);
lean_inc_ref(v_body_2692_);
lean_inc_ref(v_post_2632_);
lean_inc_ref(v_pre_2630_);
v___x_2698_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2630_, v_post_2632_, v_body_2692_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; size_t v___x_2700_; size_t v___x_2701_; uint8_t v___x_2702_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = lean_ptr_addr(v_type_2690_);
v___x_2701_ = lean_ptr_addr(v_a_2695_);
v___x_2702_ = lean_usize_dec_eq(v___x_2700_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
lean_inc(v_declName_2689_);
lean_dec_ref_known(v___y_2644_, 4);
v___x_2703_ = l_Lean_Expr_letE___override(v_declName_2689_, v_a_2695_, v_a_2697_, v_a_2699_, v_nondep_2693_);
v___x_2704_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___x_2703_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2704_;
}
else
{
size_t v___x_2705_; size_t v___x_2706_; uint8_t v___x_2707_; 
v___x_2705_ = lean_ptr_addr(v_value_2691_);
v___x_2706_ = lean_ptr_addr(v_a_2697_);
v___x_2707_ = lean_usize_dec_eq(v___x_2705_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_inc(v_declName_2689_);
lean_dec_ref_known(v___y_2644_, 4);
v___x_2708_ = l_Lean_Expr_letE___override(v_declName_2689_, v_a_2695_, v_a_2697_, v_a_2699_, v_nondep_2693_);
v___x_2709_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___x_2708_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2709_;
}
else
{
size_t v___x_2710_; size_t v___x_2711_; uint8_t v___x_2712_; 
v___x_2710_ = lean_ptr_addr(v_body_2692_);
v___x_2711_ = lean_ptr_addr(v_a_2699_);
v___x_2712_ = lean_usize_dec_eq(v___x_2710_, v___x_2711_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_inc(v_declName_2689_);
lean_dec_ref_known(v___y_2644_, 4);
v___x_2713_ = l_Lean_Expr_letE___override(v_declName_2689_, v_a_2695_, v_a_2697_, v_a_2699_, v_nondep_2693_);
v___x_2714_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___x_2713_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2714_;
}
else
{
lean_object* v___x_2715_; 
lean_dec(v_a_2699_);
lean_dec(v_a_2697_);
lean_dec(v_a_2695_);
v___x_2715_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___y_2644_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2715_;
}
}
}
}
else
{
lean_dec(v_a_2697_);
lean_dec(v_a_2695_);
lean_dec_ref_known(v___y_2644_, 4);
lean_dec_ref(v_post_2632_);
lean_dec_ref(v_pre_2630_);
return v___x_2698_;
}
}
else
{
lean_dec(v_a_2695_);
lean_dec_ref_known(v___y_2644_, 4);
lean_dec_ref(v_post_2632_);
lean_dec_ref(v_pre_2630_);
return v___x_2696_;
}
}
else
{
lean_dec_ref_known(v___y_2644_, 4);
lean_dec_ref(v_post_2632_);
lean_dec_ref(v_pre_2630_);
return v___x_2694_;
}
}
case 5:
{
lean_object* v_dummy_2716_; lean_object* v_nargs_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v_dummy_2716_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0);
v_nargs_2717_ = l_Lean_Expr_getAppNumArgs(v___y_2644_);
lean_inc(v_nargs_2717_);
v___x_2718_ = lean_mk_array(v_nargs_2717_, v_dummy_2716_);
v___x_2719_ = lean_unsigned_to_nat(1u);
v___x_2720_ = lean_nat_sub(v_nargs_2717_, v___x_2719_);
lean_dec(v_nargs_2717_);
v___x_2721_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_pre_2630_, v_post_2632_, v___y_2644_, v___x_2718_, v___x_2720_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2721_;
}
case 10:
{
lean_object* v_data_2722_; lean_object* v_expr_2723_; lean_object* v___x_2724_; 
v_data_2722_ = lean_ctor_get(v___y_2644_, 0);
v_expr_2723_ = lean_ctor_get(v___y_2644_, 1);
lean_inc_ref(v_expr_2723_);
lean_inc_ref(v_post_2632_);
lean_inc_ref(v_pre_2630_);
v___x_2724_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2630_, v_post_2632_, v_expr_2723_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; size_t v___x_2726_; size_t v___x_2727_; uint8_t v___x_2728_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2724_, 1);
v___x_2726_ = lean_ptr_addr(v_expr_2723_);
v___x_2727_ = lean_ptr_addr(v_a_2725_);
v___x_2728_ = lean_usize_dec_eq(v___x_2726_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_inc(v_data_2722_);
lean_dec_ref_known(v___y_2644_, 2);
v___x_2729_ = l_Lean_Expr_mdata___override(v_data_2722_, v_a_2725_);
v___x_2730_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___x_2729_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2730_;
}
else
{
lean_object* v___x_2731_; 
lean_dec(v_a_2725_);
v___x_2731_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___y_2644_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2731_;
}
}
else
{
lean_dec_ref_known(v___y_2644_, 2);
lean_dec_ref(v_post_2632_);
lean_dec_ref(v_pre_2630_);
return v___x_2724_;
}
}
case 11:
{
lean_object* v_typeName_2732_; lean_object* v_idx_2733_; lean_object* v_struct_2734_; lean_object* v___x_2735_; 
v_typeName_2732_ = lean_ctor_get(v___y_2644_, 0);
v_idx_2733_ = lean_ctor_get(v___y_2644_, 1);
v_struct_2734_ = lean_ctor_get(v___y_2644_, 2);
lean_inc_ref(v_struct_2734_);
lean_inc_ref(v_post_2632_);
lean_inc_ref(v_pre_2630_);
v___x_2735_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2630_, v_post_2632_, v_struct_2734_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; size_t v___x_2737_; size_t v___x_2738_; uint8_t v___x_2739_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2737_ = lean_ptr_addr(v_struct_2734_);
v___x_2738_ = lean_ptr_addr(v_a_2736_);
v___x_2739_ = lean_usize_dec_eq(v___x_2737_, v___x_2738_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_inc(v_idx_2733_);
lean_inc(v_typeName_2732_);
lean_dec_ref_known(v___y_2644_, 3);
v___x_2740_ = l_Lean_Expr_proj___override(v_typeName_2732_, v_idx_2733_, v_a_2736_);
v___x_2741_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___x_2740_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2741_;
}
else
{
lean_object* v___x_2742_; 
lean_dec(v_a_2736_);
v___x_2742_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___y_2644_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2742_;
}
}
else
{
lean_dec_ref_known(v___y_2644_, 3);
lean_dec_ref(v_post_2632_);
lean_dec_ref(v_pre_2630_);
return v___x_2735_;
}
}
default: 
{
lean_object* v___x_2743_; 
v___x_2743_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2630_, v_post_2632_, v___y_2644_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2743_;
}
}
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref(v_post_2632_);
lean_dec_ref(v_e_2631_);
lean_dec_ref(v_pre_2630_);
v_a_2755_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2638_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2638_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec_ref(v_post_2632_);
lean_dec_ref(v_e_2631_);
lean_dec_ref(v_pre_2630_);
v_a_2763_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2637_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2637_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2629_ = stack[0].m_obj;
lean_object* v_pre_2630_ = stack[1].m_obj;
lean_object* v_e_2631_ = stack[2].m_obj;
lean_object* v_post_2632_ = stack[3].m_obj;
lean_object* v___y_2633_ = stack[4].m_obj;
lean_object* v___y_2634_ = stack[5].m_obj;
lean_object* v___y_2635_ = stack[6].m_obj;
lean_object* v_res_2771_;
v_res_2771_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(v___x_2629_, v_pre_2630_, v_e_2631_, v_post_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
stack->m_obj
 = v_res_2771_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object* v___x_2772_, lean_object* v_pre_2773_, lean_object* v_e_2774_, lean_object* v_post_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(v___x_2772_, v_pre_2773_, v_e_2774_, v_post_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
return v_res_2780_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(lean_object* v_pre_2781_, lean_object* v_post_2782_, lean_object* v_e_2783_, lean_object* v_a_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
lean_inc(v_a_2784_);
v___x_2788_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2788_, 0, lean_box(0));
lean_closure_set(v___x_2788_, 1, lean_box(0));
lean_closure_set(v___x_2788_, 2, v_a_2784_);
v___x_2789_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___x_2788_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2821_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2821_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2821_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; 
v___x_2794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(v_a_2790_, v_e_2783_);
lean_dec(v_a_2790_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v___x_2795_; lean_object* v___f_2796_; lean_object* v___x_2797_; 
lean_del_object(v___x_2792_);
v___x_2795_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___closed__0));
lean_inc_ref(v_e_2783_);
v___f_2796_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed), 8, 4);
lean_closure_set(v___f_2796_, 0, v___x_2795_);
lean_closure_set(v___f_2796_, 1, v_pre_2781_);
lean_closure_set(v___f_2796_, 2, v_e_2783_);
lean_closure_set(v___f_2796_, 3, v_post_2782_);
v___x_2797_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v___f_2796_, v_a_2784_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___f_2799_; lean_object* v___x_2800_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc_n(v_a_2798_, 2);
lean_dec_ref_known(v___x_2797_, 1);
lean_inc(v_a_2784_);
v___f_2799_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2799_, 0, v_a_2784_);
lean_closure_set(v___f_2799_, 1, v_e_2783_);
lean_closure_set(v___f_2799_, 2, v_a_2798_);
v___x_2800_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___f_2799_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; 
v_unused_2808_ = lean_ctor_get(v___x_2800_, 0);
lean_dec(v_unused_2808_);
v___x_2802_ = v___x_2800_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_dec(v___x_2800_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v_a_2798_);
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2798_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_a_2798_);
v_a_2809_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2800_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2800_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
else
{
lean_dec_ref(v_e_2783_);
return v___x_2797_;
}
}
else
{
lean_object* v_val_2817_; lean_object* v___x_2819_; 
lean_dec_ref(v_e_2783_);
lean_dec_ref(v_post_2782_);
lean_dec_ref(v_pre_2781_);
v_val_2817_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_val_2817_);
lean_dec_ref_known(v___x_2794_, 1);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v_val_2817_);
v___x_2819_ = v___x_2792_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_val_2817_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec_ref(v_e_2783_);
lean_dec_ref(v_post_2782_);
lean_dec_ref(v_pre_2781_);
v_a_2822_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2789_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2789_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2781_ = stack[0].m_obj;
lean_object* v_post_2782_ = stack[1].m_obj;
lean_object* v_e_2783_ = stack[2].m_obj;
lean_object* v_a_2784_ = stack[3].m_obj;
lean_object* v___y_2785_ = stack[4].m_obj;
lean_object* v___y_2786_ = stack[5].m_obj;
lean_object* v_res_2830_;
v_res_2830_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2781_, v_post_2782_, v_e_2783_, v_a_2784_, v___y_2785_, v___y_2786_);
stack->m_obj
 = v_res_2830_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(lean_object* v_pre_2831_, lean_object* v_post_2832_, lean_object* v_e_2833_, lean_object* v_a_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v___x_2838_; 
lean_inc_ref(v_post_2832_);
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
lean_inc_ref(v_e_2833_);
v___x_2838_ = lean_apply_4(v_post_2832_, v_e_2833_, v___y_2835_, v___y_2836_, lean_box(0));
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2857_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2857_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2857_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
switch(lean_obj_tag(v_a_2839_))
{
case 0:
{
lean_object* v_e_2843_; lean_object* v___x_2845_; 
lean_dec_ref(v_e_2833_);
lean_dec_ref(v_post_2832_);
lean_dec_ref(v_pre_2831_);
v_e_2843_ = lean_ctor_get(v_a_2839_, 0);
lean_inc_ref(v_e_2843_);
lean_dec_ref_known(v_a_2839_, 1);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v_e_2843_);
v___x_2845_ = v___x_2841_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_e_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
case 1:
{
lean_object* v_e_2847_; lean_object* v___x_2848_; 
lean_del_object(v___x_2841_);
lean_dec_ref(v_e_2833_);
v_e_2847_ = lean_ctor_get(v_a_2839_, 0);
lean_inc_ref(v_e_2847_);
lean_dec_ref_known(v_a_2839_, 1);
v___x_2848_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2831_, v_post_2832_, v_e_2847_, v_a_2834_, v___y_2835_, v___y_2836_);
return v___x_2848_;
}
default: 
{
lean_object* v_e_x3f_2849_; 
lean_dec_ref(v_post_2832_);
lean_dec_ref(v_pre_2831_);
v_e_x3f_2849_ = lean_ctor_get(v_a_2839_, 0);
lean_inc(v_e_x3f_2849_);
lean_dec_ref_known(v_a_2839_, 1);
if (lean_obj_tag(v_e_x3f_2849_) == 0)
{
lean_object* v___x_2851_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v_e_2833_);
v___x_2851_ = v___x_2841_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_e_2833_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
else
{
lean_object* v_val_2853_; lean_object* v___x_2855_; 
lean_dec_ref(v_e_2833_);
v_val_2853_ = lean_ctor_get(v_e_x3f_2849_, 0);
lean_inc(v_val_2853_);
lean_dec_ref_known(v_e_x3f_2849_, 1);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v_val_2853_);
v___x_2855_ = v___x_2841_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_val_2853_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec_ref(v_e_2833_);
lean_dec_ref(v_post_2832_);
lean_dec_ref(v_pre_2831_);
v_a_2858_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2838_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2838_);
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
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2831_ = stack[0].m_obj;
lean_object* v_post_2832_ = stack[1].m_obj;
lean_object* v_e_2833_ = stack[2].m_obj;
lean_object* v_a_2834_ = stack[3].m_obj;
lean_object* v___y_2835_ = stack[4].m_obj;
lean_object* v___y_2836_ = stack[5].m_obj;
lean_object* v_res_2866_;
v_res_2866_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2831_, v_post_2832_, v_e_2833_, v_a_2834_, v___y_2835_, v___y_2836_);
stack->m_obj
 = v_res_2866_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_2867_, lean_object* v_post_2868_, lean_object* v_e_2869_, lean_object* v_a_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2867_, v_post_2868_, v_e_2869_, v_a_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v_a_2870_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_2875_, lean_object* v_post_2876_, lean_object* v_sz_2877_, lean_object* v_i_2878_, lean_object* v_bs_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
size_t v_sz_boxed_2884_; size_t v_i_boxed_2885_; lean_object* v_res_2886_; 
v_sz_boxed_2884_ = lean_unbox_usize(v_sz_2877_);
lean_dec(v_sz_2877_);
v_i_boxed_2885_ = lean_unbox_usize(v_i_2878_);
lean_dec(v_i_2878_);
v_res_2886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_2875_, v_post_2876_, v_sz_boxed_2884_, v_i_boxed_2885_, v_bs_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_2887_, lean_object* v_post_2888_, lean_object* v_x_2889_, lean_object* v_x_2890_, lean_object* v_x_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_pre_2887_, v_post_2888_, v_x_2889_, v_x_2890_, v_x_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___boxed(lean_object* v_pre_2897_, lean_object* v_post_2898_, lean_object* v_e_2899_, lean_object* v_a_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2897_, v_post_2898_, v_e_2899_, v_a_2900_, v___y_2901_, v___y_2902_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec(v_a_2900_);
return v_res_2904_;
}
}
lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_object* v_00_u03b1_2905_, lean_object* v_x_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_apply_1(v_x_2906_, lean_box(0));
v___x_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT void l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2906_ = stack[1].m_obj;
lean_object* v___y_2907_ = stack[2].m_obj;
lean_object* v___y_2908_ = stack[3].m_obj;
lean_object* v_res_2912_;
v_res_2912_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v_x_2906_, v___y_2907_, v___y_2908_);
stack->m_obj
 = v_res_2912_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2913_, lean_object* v_x_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(v_00_u03b1_2913_, v_x_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
return v_res_2918_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__1, &l_Lean_Expr_checkMaxShared___closed__1_once, _init_l_Lean_Expr_checkMaxShared___closed__1);
v___x_2920_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2920_, 0, lean_box(0));
lean_closure_set(v___x_2920_, 1, lean_box(0));
lean_closure_set(v___x_2920_, 2, v___x_2919_);
return v___x_2920_;
}
}
lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(lean_object* v_input_2921_, lean_object* v_pre_2922_, lean_object* v_post_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v_a_2929_; lean_object* v___x_2930_; 
v___x_2927_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0);
v___x_2928_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_2927_, v___y_2924_, v___y_2925_);
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref(v___x_2928_);
v___x_2930_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2922_, v_post_2923_, v_input_2921_, v_a_2929_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2930_, 1);
v___x_2932_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2932_, 0, lean_box(0));
lean_closure_set(v___x_2932_, 1, lean_box(0));
lean_closure_set(v___x_2932_, 2, v_a_2929_);
v___x_2933_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_2932_, v___y_2924_, v___y_2925_);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2940_ == 0)
{
lean_object* v_unused_2941_; 
v_unused_2941_ = lean_ctor_get(v___x_2933_, 0);
lean_dec(v_unused_2941_);
v___x_2935_ = v___x_2933_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_dec(v___x_2933_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 0, v_a_2931_);
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2931_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
else
{
lean_dec(v_a_2929_);
return v___x_2930_;
}
}
}
LEAN_EXPORT void l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_2921_ = stack[0].m_obj;
lean_object* v_pre_2922_ = stack[1].m_obj;
lean_object* v_post_2923_ = stack[2].m_obj;
lean_object* v___y_2924_ = stack[3].m_obj;
lean_object* v___y_2925_ = stack[4].m_obj;
lean_object* v_res_2942_;
v_res_2942_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_input_2921_, v_pre_2922_, v_post_2923_, v___y_2924_, v___y_2925_);
stack->m_obj
 = v_res_2942_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___boxed(lean_object* v_input_2943_, lean_object* v_pre_2944_, lean_object* v_post_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_input_2943_, v_pre_2944_, v_post_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
return v_res_2949_;
}
}
lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object* v_e_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
uint8_t v___x_2956_; 
v___x_2956_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_2952_);
if (v___x_2956_ == 0)
{
lean_object* v_pre_2957_; lean_object* v___f_2958_; lean_object* v___x_2959_; 
v_pre_2957_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__0));
v___f_2958_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__1));
v___x_2959_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_e_2952_, v_pre_2957_, v___f_2958_, v_a_2953_, v_a_2954_);
return v___x_2959_;
}
else
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2960_, 0, v_e_2952_);
return v___x_2960_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_normalizeLevels_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2952_ = stack[0].m_obj;
lean_object* v_a_2953_ = stack[1].m_obj;
lean_object* v_a_2954_ = stack[2].m_obj;
lean_object* v_res_2961_;
v_res_2961_ = l_Lean_Meta_Sym_normalizeLevels(v_e_2952_, v_a_2953_, v_a_2954_);
stack->m_obj
 = v_res_2961_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___boxed(lean_object* v_e_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Lean_Meta_Sym_normalizeLevels(v_e_2962_, v_a_2963_, v_a_2964_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_2967_, lean_object* v_m_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(v_m_2968_, v_a_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2971_, lean_object* v_m_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_00_u03b2_2971_, v_m_2972_, v_a_2973_);
lean_dec_ref(v_a_2973_);
lean_dec_ref(v_m_2972_);
return v_res_2974_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_2975_, lean_object* v_ref_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2976_);
return v___x_2980_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2976_ = stack[1].m_obj;
lean_object* v___y_2977_ = stack[2].m_obj;
lean_object* v___y_2978_ = stack[3].m_obj;
lean_object* v_res_2981_;
v_res_2981_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8(lean_box(0), v_ref_2976_, v___y_2977_, v___y_2978_);
stack->m_obj
 = v_res_2981_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2982_, lean_object* v_ref_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_2982_, v_ref_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
return v_res_2987_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
return v___x_2992_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2989_ = stack[1].m_obj;
lean_object* v___y_2990_ = stack[2].m_obj;
lean_object* v_res_2993_;
v_res_2993_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9(lean_box(0), v___y_2989_, v___y_2990_);
stack->m_obj
 = v_res_2993_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9(v_00_u03b1_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
return v_res_2998_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6(lean_object* v_00_u03b1_2999_, lean_object* v_x_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v_x_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3000_ = stack[1].m_obj;
lean_object* v___y_3001_ = stack[2].m_obj;
lean_object* v___y_3002_ = stack[3].m_obj;
lean_object* v___y_3003_ = stack[4].m_obj;
lean_object* v_res_3006_;
v_res_3006_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6(lean_box(0), v_x_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
stack->m_obj
 = v_res_3006_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3007_, lean_object* v_x_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6(v_00_u03b1_3007_, v_x_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_3014_, lean_object* v_m_3015_, lean_object* v_a_3016_, lean_object* v_b_3017_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v_m_3015_, v_a_3016_, v_b_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_3019_, lean_object* v_a_3020_, lean_object* v_x_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(v_a_3020_, v_x_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3023_, lean_object* v_a_3024_, lean_object* v_x_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5(v_00_u03b2_3023_, v_a_3024_, v_x_3025_);
lean_dec(v_x_3025_);
lean_dec_ref(v_a_3024_);
return v_res_3026_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_3027_, lean_object* v_a_3028_, lean_object* v_x_3029_){
_start:
{
uint8_t v___x_3030_; 
v___x_3030_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_a_3028_, v_x_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3028_ = stack[1].m_obj;
lean_object* v_x_3029_ = stack[2].m_obj;
uint8_t v_res_3031_;
v_res_3031_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(lean_box(0), v_a_3028_, v_x_3029_);
stack->m_num = v_res_3031_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3032_, lean_object* v_a_3033_, lean_object* v_x_3034_){
_start:
{
uint8_t v_res_3035_; lean_object* v_r_3036_; 
v_res_3035_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_3032_, v_a_3033_, v_x_3034_);
lean_dec(v_x_3034_);
lean_dec_ref(v_a_3033_);
v_r_3036_ = lean_box(v_res_3035_);
return v_r_3036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_3037_, lean_object* v_data_3038_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12___redArg(v_data_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13(lean_object* v_00_u03b2_3040_, lean_object* v_a_3041_, lean_object* v_b_3042_, lean_object* v_x_3043_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(v_a_3041_, v_b_3042_, v_x_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13(lean_object* v_00_u03b2_3045_, lean_object* v_i_3046_, lean_object* v_source_3047_, lean_object* v_target_3048_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v_i_3046_, v_source_3047_, v_target_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14(lean_object* v_00_u03b2_3050_, lean_object* v_x_3051_, lean_object* v_x_3052_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_x_3051_, v_x_3052_);
return v___x_3053_;
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
