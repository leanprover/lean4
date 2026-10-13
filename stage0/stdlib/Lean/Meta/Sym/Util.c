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
size_t v_x_2263__boxed_1368_; size_t v_x_2264__boxed_1369_; lean_object* v_res_1370_; 
v_x_2263__boxed_1368_ = lean_unbox_usize(v_x_1364_);
lean_dec(v_x_1364_);
v_x_2264__boxed_1369_ = lean_unbox_usize(v_x_1365_);
lean_dec(v_x_1365_);
v_res_1370_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1363_, v_x_2263__boxed_1368_, v_x_2264__boxed_1369_, v_x_1366_, v_x_1367_);
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
lean_object* v___x_1382_; lean_object* v_mctx_1383_; lean_object* v_cache_1384_; lean_object* v_zetaDeltaFVarIds_1385_; lean_object* v_postponed_1386_; lean_object* v_diag_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1417_; 
v___x_1382_ = lean_st_ref_take(v___y_1380_);
v_mctx_1383_ = lean_ctor_get(v___x_1382_, 0);
v_cache_1384_ = lean_ctor_get(v___x_1382_, 1);
v_zetaDeltaFVarIds_1385_ = lean_ctor_get(v___x_1382_, 2);
v_postponed_1386_ = lean_ctor_get(v___x_1382_, 3);
v_diag_1387_ = lean_ctor_get(v___x_1382_, 4);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1389_ = v___x_1382_;
v_isShared_1390_ = v_isSharedCheck_1417_;
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
v_isShared_1390_ = v_isSharedCheck_1417_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_depth_1391_; lean_object* v_levelAssignDepth_1392_; lean_object* v_lmvarCounter_1393_; lean_object* v_mvarCounter_1394_; lean_object* v_lDecls_1395_; lean_object* v_decls_1396_; lean_object* v_userNames_1397_; lean_object* v_lAssignment_1398_; lean_object* v_eAssignment_1399_; lean_object* v_dAssignment_1400_; lean_object* v_instanceTypedMVars_1401_; lean_object* v_synthNormMemo_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1416_; 
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
v_synthNormMemo_1402_ = lean_ctor_get(v_mctx_1383_, 11);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_mctx_1383_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1404_ = v_mctx_1383_;
v_isShared_1405_ = v_isSharedCheck_1416_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_synthNormMemo_1402_);
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
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1416_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1406_ = lean_box(0);
v___x_1407_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_eAssignment_1399_, v_mvarId_1378_, v_val_1379_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 8, v___x_1407_);
v___x_1409_ = v___x_1404_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_depth_1391_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_levelAssignDepth_1392_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_lmvarCounter_1393_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_mvarCounter_1394_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v_lDecls_1395_);
lean_ctor_set(v_reuseFailAlloc_1415_, 5, v_decls_1396_);
lean_ctor_set(v_reuseFailAlloc_1415_, 6, v_userNames_1397_);
lean_ctor_set(v_reuseFailAlloc_1415_, 7, v_lAssignment_1398_);
lean_ctor_set(v_reuseFailAlloc_1415_, 8, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1415_, 9, v_dAssignment_1400_);
lean_ctor_set(v_reuseFailAlloc_1415_, 10, v_instanceTypedMVars_1401_);
lean_ctor_set(v_reuseFailAlloc_1415_, 11, v_synthNormMemo_1402_);
v___x_1409_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1411_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1409_);
v___x_1411_ = v___x_1389_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_cache_1384_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_zetaDeltaFVarIds_1385_);
lean_ctor_set(v_reuseFailAlloc_1414_, 3, v_postponed_1386_);
lean_ctor_set(v_reuseFailAlloc_1414_, 4, v_diag_1387_);
v___x_1411_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_st_ref_put(v___y_1380_, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1406_);
return v___x_1413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg___boxed(lean_object* v_mvarId_1418_, lean_object* v_val_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1418_, v_val_1419_, v___y_1420_);
lean_dec(v___y_1420_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object* v_mvarId_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v___x_1431_; 
lean_inc(v_mvarId_1423_);
v___x_1431_ = l_Lean_MVarId_getDecl(v_mvarId_1423_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v_userName_1433_; lean_object* v_lctx_1434_; lean_object* v_type_1435_; lean_object* v_localInstances_1436_; lean_object* v___x_1437_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v_userName_1433_ = lean_ctor_get(v_a_1432_, 0);
lean_inc(v_userName_1433_);
v_lctx_1434_ = lean_ctor_get(v_a_1432_, 1);
lean_inc_ref(v_lctx_1434_);
v_type_1435_ = lean_ctor_get(v_a_1432_, 2);
lean_inc_ref(v_type_1435_);
v_localInstances_1436_ = lean_ctor_get(v_a_1432_, 4);
lean_inc_ref(v_localInstances_1436_);
lean_dec(v_a_1432_);
v___x_1437_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_1434_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1439_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = l_Lean_Meta_Sym_preprocessExpr(v_type_1435_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v___x_1441_ = 2;
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_1438_, v_localInstances_1436_, v_a_1440_, v___x_1441_, v_userName_1433_, v___x_1442_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1453_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc_n(v_a_1444_, 2);
lean_dec_ref_known(v___x_1443_, 1);
v___x_1445_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1423_, v_a_1444_, v_a_1427_);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v___x_1445_, 0);
lean_dec(v_unused_1454_);
v___x_1447_ = v___x_1445_;
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
else
{
lean_dec(v___x_1445_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = l_Lean_Expr_mvarId_x21(v_a_1444_);
lean_dec(v_a_1444_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1449_);
v___x_1451_ = v___x_1447_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_mvarId_1423_);
v_a_1455_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1443_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1443_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_a_1438_);
lean_dec_ref(v_localInstances_1436_);
lean_dec(v_userName_1433_);
lean_dec(v_mvarId_1423_);
v_a_1463_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1439_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1439_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v_localInstances_1436_);
lean_dec_ref(v_type_1435_);
lean_dec(v_userName_1433_);
lean_dec(v_mvarId_1423_);
v_a_1471_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1437_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1437_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_mvarId_1423_);
v_a_1479_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1431_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1431_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar___boxed(lean_object* v_mvarId_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(lean_object* v_mvarId_1496_, lean_object* v_val_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_1496_, v_val_1497_, v___y_1501_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___boxed(lean_object* v_mvarId_1506_, lean_object* v_val_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(v_mvarId_1506_, v_val_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0(lean_object* v_00_u03b2_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_, lean_object* v_x_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_x_1517_, v_x_1518_, v_x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1521_, lean_object* v_x_1522_, size_t v_x_1523_, size_t v_x_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_1522_, v_x_1523_, v_x_1524_, v_x_1525_, v_x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_){
_start:
{
size_t v_x_2612__boxed_1534_; size_t v_x_2613__boxed_1535_; lean_object* v_res_1536_; 
v_x_2612__boxed_1534_ = lean_unbox_usize(v_x_1530_);
lean_dec(v_x_1530_);
v_x_2613__boxed_1535_ = lean_unbox_usize(v_x_1531_);
lean_dec(v_x_1531_);
v_res_1536_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(v_00_u03b2_1528_, v_x_1529_, v_x_2612__boxed_1534_, v_x_2613__boxed_1535_, v_x_1532_, v_x_1533_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1537_, lean_object* v_n_1538_, lean_object* v_k_1539_, lean_object* v_v_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1538_, v_k_1539_, v_v_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1542_, size_t v_depth_1543_, lean_object* v_keys_1544_, lean_object* v_vals_1545_, lean_object* v_heq_1546_, lean_object* v_i_1547_, lean_object* v_entries_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1543_, v_keys_1544_, v_vals_1545_, v_i_1547_, v_entries_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1550_, lean_object* v_depth_1551_, lean_object* v_keys_1552_, lean_object* v_vals_1553_, lean_object* v_heq_1554_, lean_object* v_i_1555_, lean_object* v_entries_1556_){
_start:
{
size_t v_depth_boxed_1557_; lean_object* v_res_1558_; 
v_depth_boxed_1557_ = lean_unbox_usize(v_depth_1551_);
lean_dec(v_depth_1551_);
v_res_1558_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1550_, v_depth_boxed_1557_, v_keys_1552_, v_vals_1553_, v_heq_1554_, v_i_1555_, v_entries_1556_);
lean_dec_ref(v_vals_1553_);
lean_dec_ref(v_keys_1552_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1559_, lean_object* v_x_1560_, lean_object* v_x_1561_, lean_object* v_x_1562_, lean_object* v_x_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1560_, v_x_1561_, v_x_1562_, v_x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(lean_object* v_msgData_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; lean_object* v_env_1572_; uint8_t v___x_1573_; lean_object* v_env_1574_; lean_object* v___x_1575_; lean_object* v_toCold_1576_; lean_object* v_mctx_1577_; lean_object* v_lctx_1578_; lean_object* v_options_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1571_ = lean_st_ref_get(v___y_1569_);
v_env_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc_ref(v_env_1572_);
lean_dec(v___x_1571_);
v___x_1573_ = 0;
v_env_1574_ = l_Lean_Environment_setRecordingDeps(v_env_1572_, v___x_1573_);
v___x_1575_ = lean_st_ref_get(v___y_1567_);
v_toCold_1576_ = lean_ctor_get(v___y_1568_, 0);
v_mctx_1577_ = lean_ctor_get(v___x_1575_, 0);
lean_inc_ref(v_mctx_1577_);
lean_dec(v___x_1575_);
v_lctx_1578_ = lean_ctor_get(v___y_1566_, 2);
v_options_1579_ = lean_ctor_get(v_toCold_1576_, 2);
lean_inc_ref(v_options_1579_);
lean_inc_ref(v_lctx_1578_);
v___x_1580_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1580_, 0, v_env_1574_);
lean_ctor_set(v___x_1580_, 1, v_mctx_1577_);
lean_ctor_set(v___x_1580_, 2, v_lctx_1578_);
lean_ctor_set(v___x_1580_, 3, v_options_1579_);
v___x_1581_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v_msgData_1565_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0___boxed(lean_object* v_msgData_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msgData_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(lean_object* v_msg_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_ref_1596_; lean_object* v___x_1597_; lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1606_; 
v_ref_1596_ = lean_ctor_get(v___y_1593_, 2);
v___x_1597_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0_spec__0(v_msg_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
lean_inc(v_ref_1596_);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v_ref_1596_);
lean_ctor_set(v___x_1602_, 1, v_a_1598_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 1);
lean_ctor_set(v___x_1600_, 0, v___x_1602_);
v___x_1604_ = v___x_1600_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(lean_object* v_msg_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
return v_res_1613_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0));
v___x_1616_ = l_Lean_stringToMessageData(v___x_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(lean_object* v_msg_1620_, lean_object* v_e_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v___y_1630_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2));
v___x_1638_ = lean_string_dec_eq(v_msg_1620_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1639_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3));
v___x_1640_ = lean_string_append(v___x_1639_, v_msg_1620_);
lean_dec_ref(v_msg_1620_);
v___x_1641_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__4));
v___x_1642_ = lean_string_append(v___x_1640_, v___x_1641_);
v___y_1630_ = v___x_1642_;
goto v___jp_1629_;
}
else
{
v___y_1630_ = v_msg_1620_;
goto v___jp_1629_;
}
v___jp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1631_ = l_Lean_stringToMessageData(v___y_1630_);
v___x_1632_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = l_Lean_indentExpr(v_e_1621_);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v___x_1635_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(lean_object* v_msg_1643_, lean_object* v_e_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1643_, v_e_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_object* v_00_u03b1_1653_, lean_object* v_msg_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_1654_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(lean_object* v_00_u03b1_1663_, lean_object* v_msg_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(v_00_u03b1_1663_, v_msg_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1673_, lean_object* v_vals_1674_, lean_object* v_i_1675_, lean_object* v_k_1676_){
_start:
{
lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1677_ = lean_array_get_size(v_keys_1673_);
v___x_1678_ = lean_nat_dec_lt(v_i_1675_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_dec(v_i_1675_);
v___x_1679_ = lean_box(0);
return v___x_1679_;
}
else
{
lean_object* v_k_x27_1680_; uint8_t v___x_1681_; 
v_k_x27_1680_ = lean_array_fget_borrowed(v_keys_1673_, v_i_1675_);
v___x_1681_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_1676_, v_k_x27_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_unsigned_to_nat(1u);
v___x_1683_ = lean_nat_add(v_i_1675_, v___x_1682_);
lean_dec(v_i_1675_);
v_i_1675_ = v___x_1683_;
goto _start;
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_array_fget_borrowed(v_vals_1674_, v_i_1675_);
lean_dec(v_i_1675_);
lean_inc(v___x_1685_);
lean_inc(v_k_x27_1680_);
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_k_x27_1680_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1688_, lean_object* v_vals_1689_, lean_object* v_i_1690_, lean_object* v_k_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_1688_, v_vals_1689_, v_i_1690_, v_k_1691_);
lean_dec_ref(v_k_1691_);
lean_dec_ref(v_vals_1689_);
lean_dec_ref(v_keys_1688_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(lean_object* v_x_1693_, size_t v_x_1694_, lean_object* v_x_1695_){
_start:
{
if (lean_obj_tag(v_x_1693_) == 0)
{
lean_object* v_es_1696_; lean_object* v___x_1697_; size_t v___x_1698_; size_t v___x_1699_; lean_object* v_j_1700_; lean_object* v___x_1701_; 
v_es_1696_ = lean_ctor_get(v_x_1693_, 0);
v___x_1697_ = lean_box(2);
v___x_1698_ = ((size_t)31ULL);
v___x_1699_ = lean_usize_land(v_x_1694_, v___x_1698_);
v_j_1700_ = lean_usize_to_nat(v___x_1699_);
v___x_1701_ = lean_array_get_borrowed(v___x_1697_, v_es_1696_, v_j_1700_);
lean_dec(v_j_1700_);
switch(lean_obj_tag(v___x_1701_))
{
case 0:
{
lean_object* v_key_1702_; lean_object* v_val_1703_; uint8_t v___x_1704_; 
v_key_1702_ = lean_ctor_get(v___x_1701_, 0);
v_val_1703_ = lean_ctor_get(v___x_1701_, 1);
v___x_1704_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_1695_, v_key_1702_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_box(0);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_inc(v_val_1703_);
lean_inc(v_key_1702_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_key_1702_);
lean_ctor_set(v___x_1706_, 1, v_val_1703_);
v___x_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
return v___x_1707_;
}
}
case 1:
{
lean_object* v_node_1708_; size_t v___x_1709_; size_t v___x_1710_; 
v_node_1708_ = lean_ctor_get(v___x_1701_, 0);
v___x_1709_ = ((size_t)5ULL);
v___x_1710_ = lean_usize_shift_right(v_x_1694_, v___x_1709_);
v_x_1693_ = v_node_1708_;
v_x_1694_ = v___x_1710_;
goto _start;
}
default: 
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_box(0);
return v___x_1712_;
}
}
}
else
{
lean_object* v_ks_1713_; lean_object* v_vs_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_ks_1713_ = lean_ctor_get(v_x_1693_, 0);
v_vs_1714_ = lean_ctor_get(v_x_1693_, 1);
v___x_1715_ = lean_unsigned_to_nat(0u);
v___x_1716_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_ks_1713_, v_vs_1714_, v___x_1715_, v_x_1695_);
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_){
_start:
{
size_t v_x_7386__boxed_1720_; lean_object* v_res_1721_; 
v_x_7386__boxed_1720_ = lean_unbox_usize(v_x_1718_);
lean_dec(v_x_1718_);
v_res_1721_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_1717_, v_x_7386__boxed_1720_, v_x_1719_);
lean_dec_ref(v_x_1719_);
lean_dec_ref(v_x_1717_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
uint64_t v___x_1724_; size_t v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_1723_);
v___x_1725_ = lean_uint64_to_usize(v___x_1724_);
v___x_1726_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_1722_, v___x_1725_, v_x_1723_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg___boxed(lean_object* v_x_1727_, lean_object* v_x_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_1727_, v_x_1728_);
lean_dec_ref(v_x_1728_);
lean_dec_ref(v_x_1727_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0(lean_object* v_msg_1730_, lean_object* v_e_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v___y_1744_; lean_object* v___x_1753_; lean_object* v_share_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_st_ref_get(v___y_1733_);
v_share_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc_ref(v_share_1754_);
lean_dec(v___x_1753_);
v___x_1755_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_share_1754_, v_e_1731_);
lean_dec_ref(v_share_1754_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v___x_1756_; 
v___x_1756_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1730_, v_e_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
v___y_1744_ = v___x_1756_;
goto v___jp_1743_;
}
else
{
lean_object* v_val_1757_; lean_object* v_fst_1758_; size_t v___x_1759_; size_t v___x_1760_; uint8_t v___x_1761_; 
v_val_1757_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_val_1757_);
lean_dec_ref_known(v___x_1755_, 1);
v_fst_1758_ = lean_ctor_get(v_val_1757_, 0);
lean_inc(v_fst_1758_);
lean_dec(v_val_1757_);
v___x_1759_ = lean_ptr_addr(v_fst_1758_);
lean_dec(v_fst_1758_);
v___x_1760_ = lean_ptr_addr(v_e_1731_);
v___x_1761_ = lean_usize_dec_eq(v___x_1759_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; 
v___x_1762_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_1730_, v_e_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
v___y_1744_ = v___x_1762_;
goto v___jp_1743_;
}
else
{
lean_dec_ref(v_e_1731_);
lean_dec_ref(v_msg_1730_);
goto v___jp_1739_;
}
}
v___jp_1739_:
{
uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = 1;
v___x_1741_ = lean_box(v___x_1740_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
return v___x_1742_;
}
v___jp_1743_:
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
v_a_1745_ = lean_ctor_get(v___y_1744_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___y_1744_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___y_1744_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___y_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0___boxed(lean_object* v_msg_1763_, lean_object* v_e_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Expr_checkMaxShared___lam__0(v_msg_1763_, v_e_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(lean_object* v_a_1773_, lean_object* v_x_1774_){
_start:
{
if (lean_obj_tag(v_x_1774_) == 0)
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_box(0);
return v___x_1775_;
}
else
{
lean_object* v_key_1776_; lean_object* v_value_1777_; lean_object* v_tail_1778_; uint8_t v___x_1779_; 
v_key_1776_ = lean_ctor_get(v_x_1774_, 0);
v_value_1777_ = lean_ctor_get(v_x_1774_, 1);
v_tail_1778_ = lean_ctor_get(v_x_1774_, 2);
v___x_1779_ = lean_expr_eqv(v_key_1776_, v_a_1773_);
if (v___x_1779_ == 0)
{
v_x_1774_ = v_tail_1778_;
goto _start;
}
else
{
lean_object* v___x_1781_; 
lean_inc(v_value_1777_);
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_value_1777_);
return v___x_1781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_1782_, lean_object* v_x_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_1782_, v_x_1783_);
lean_dec(v_x_1783_);
lean_dec_ref(v_a_1782_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(lean_object* v_m_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_buckets_1787_; lean_object* v___x_1788_; uint64_t v___x_1789_; uint64_t v___x_1790_; uint64_t v___x_1791_; uint64_t v_fold_1792_; uint64_t v___x_1793_; uint64_t v___x_1794_; uint64_t v___x_1795_; size_t v___x_1796_; size_t v___x_1797_; size_t v___x_1798_; size_t v___x_1799_; size_t v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_buckets_1787_ = lean_ctor_get(v_m_1785_, 1);
v___x_1788_ = lean_array_get_size(v_buckets_1787_);
v___x_1789_ = l_Lean_Expr_hash(v_a_1786_);
v___x_1790_ = 32ULL;
v___x_1791_ = lean_uint64_shift_right(v___x_1789_, v___x_1790_);
v_fold_1792_ = lean_uint64_xor(v___x_1789_, v___x_1791_);
v___x_1793_ = 16ULL;
v___x_1794_ = lean_uint64_shift_right(v_fold_1792_, v___x_1793_);
v___x_1795_ = lean_uint64_xor(v_fold_1792_, v___x_1794_);
v___x_1796_ = lean_uint64_to_usize(v___x_1795_);
v___x_1797_ = lean_usize_of_nat(v___x_1788_);
v___x_1798_ = ((size_t)1ULL);
v___x_1799_ = lean_usize_sub(v___x_1797_, v___x_1798_);
v___x_1800_ = lean_usize_land(v___x_1796_, v___x_1799_);
v___x_1801_ = lean_array_uget_borrowed(v_buckets_1787_, v___x_1800_);
v___x_1802_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_1786_, v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(lean_object* v_m_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_1803_, v_a_1804_);
lean_dec_ref(v_a_1804_);
lean_dec_ref(v_m_1803_);
return v_res_1805_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(lean_object* v_a_1806_, lean_object* v_x_1807_){
_start:
{
if (lean_obj_tag(v_x_1807_) == 0)
{
uint8_t v___x_1808_; 
v___x_1808_ = 0;
return v___x_1808_;
}
else
{
lean_object* v_key_1809_; lean_object* v_tail_1810_; uint8_t v___x_1811_; 
v_key_1809_ = lean_ctor_get(v_x_1807_, 0);
v_tail_1810_ = lean_ctor_get(v_x_1807_, 2);
v___x_1811_ = lean_expr_eqv(v_key_1809_, v_a_1806_);
if (v___x_1811_ == 0)
{
v_x_1807_ = v_tail_1810_;
goto _start;
}
else
{
return v___x_1811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_a_1813_, lean_object* v_x_1814_){
_start:
{
uint8_t v_res_1815_; lean_object* v_r_1816_; 
v_res_1815_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_1813_, v_x_1814_);
lean_dec(v_x_1814_);
lean_dec_ref(v_a_1813_);
v_r_1816_ = lean_box(v_res_1815_);
return v_r_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(lean_object* v_a_1817_, lean_object* v_b_1818_, lean_object* v_x_1819_){
_start:
{
if (lean_obj_tag(v_x_1819_) == 0)
{
lean_dec(v_b_1818_);
lean_dec_ref(v_a_1817_);
return v_x_1819_;
}
else
{
lean_object* v_key_1820_; lean_object* v_value_1821_; lean_object* v_tail_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1834_; 
v_key_1820_ = lean_ctor_get(v_x_1819_, 0);
v_value_1821_ = lean_ctor_get(v_x_1819_, 1);
v_tail_1822_ = lean_ctor_get(v_x_1819_, 2);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_x_1819_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1824_ = v_x_1819_;
v_isShared_1825_ = v_isSharedCheck_1834_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_tail_1822_);
lean_inc(v_value_1821_);
lean_inc(v_key_1820_);
lean_dec(v_x_1819_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1834_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
uint8_t v___x_1826_; 
v___x_1826_ = lean_expr_eqv(v_key_1820_, v_a_1817_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1827_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_1817_, v_b_1818_, v_tail_1822_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 2, v___x_1827_);
v___x_1829_ = v___x_1824_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_key_1820_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_value_1821_);
lean_ctor_set(v_reuseFailAlloc_1830_, 2, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
else
{
lean_object* v___x_1832_; 
lean_dec(v_value_1821_);
lean_dec(v_key_1820_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 1, v_b_1818_);
lean_ctor_set(v___x_1824_, 0, v_a_1817_);
v___x_1832_ = v___x_1824_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1817_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_b_1818_);
lean_ctor_set(v_reuseFailAlloc_1833_, 2, v_tail_1822_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
if (lean_obj_tag(v_x_1836_) == 0)
{
return v_x_1835_;
}
else
{
lean_object* v_key_1837_; lean_object* v_value_1838_; lean_object* v_tail_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1862_; 
v_key_1837_ = lean_ctor_get(v_x_1836_, 0);
v_value_1838_ = lean_ctor_get(v_x_1836_, 1);
v_tail_1839_ = lean_ctor_get(v_x_1836_, 2);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_x_1836_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1841_ = v_x_1836_;
v_isShared_1842_ = v_isSharedCheck_1862_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_tail_1839_);
lean_inc(v_value_1838_);
lean_inc(v_key_1837_);
lean_dec(v_x_1836_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1862_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; uint64_t v___x_1844_; uint64_t v___x_1845_; uint64_t v___x_1846_; uint64_t v_fold_1847_; uint64_t v___x_1848_; uint64_t v___x_1849_; uint64_t v___x_1850_; size_t v___x_1851_; size_t v___x_1852_; size_t v___x_1853_; size_t v___x_1854_; size_t v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1843_ = lean_array_get_size(v_x_1835_);
v___x_1844_ = l_Lean_Expr_hash(v_key_1837_);
v___x_1845_ = 32ULL;
v___x_1846_ = lean_uint64_shift_right(v___x_1844_, v___x_1845_);
v_fold_1847_ = lean_uint64_xor(v___x_1844_, v___x_1846_);
v___x_1848_ = 16ULL;
v___x_1849_ = lean_uint64_shift_right(v_fold_1847_, v___x_1848_);
v___x_1850_ = lean_uint64_xor(v_fold_1847_, v___x_1849_);
v___x_1851_ = lean_uint64_to_usize(v___x_1850_);
v___x_1852_ = lean_usize_of_nat(v___x_1843_);
v___x_1853_ = ((size_t)1ULL);
v___x_1854_ = lean_usize_sub(v___x_1852_, v___x_1853_);
v___x_1855_ = lean_usize_land(v___x_1851_, v___x_1854_);
v___x_1856_ = lean_array_uget_borrowed(v_x_1835_, v___x_1855_);
lean_inc(v___x_1856_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 2, v___x_1856_);
v___x_1858_ = v___x_1841_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_key_1837_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_value_1838_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_array_uset(v_x_1835_, v___x_1855_, v___x_1858_);
v_x_1835_ = v___x_1859_;
v_x_1836_ = v_tail_1839_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(lean_object* v_i_1863_, lean_object* v_source_1864_, lean_object* v_target_1865_){
_start:
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = lean_array_get_size(v_source_1864_);
v___x_1867_ = lean_nat_dec_lt(v_i_1863_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_dec_ref(v_source_1864_);
lean_dec(v_i_1863_);
return v_target_1865_;
}
else
{
lean_object* v_es_1868_; lean_object* v___x_1869_; lean_object* v_source_1870_; lean_object* v_target_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_es_1868_ = lean_array_fget(v_source_1864_, v_i_1863_);
v___x_1869_ = lean_box(0);
v_source_1870_ = lean_array_fset(v_source_1864_, v_i_1863_, v___x_1869_);
v_target_1871_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_target_1865_, v_es_1868_);
v___x_1872_ = lean_unsigned_to_nat(1u);
v___x_1873_ = lean_nat_add(v_i_1863_, v___x_1872_);
lean_dec(v_i_1863_);
v_i_1863_ = v___x_1873_;
v_source_1864_ = v_source_1870_;
v_target_1865_ = v_target_1871_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(lean_object* v_data_1875_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v_nbuckets_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1876_ = lean_array_get_size(v_data_1875_);
v___x_1877_ = lean_unsigned_to_nat(2u);
v_nbuckets_1878_ = lean_nat_mul(v___x_1876_, v___x_1877_);
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = lean_box(0);
v___x_1881_ = lean_mk_array(v_nbuckets_1878_, v___x_1880_);
v___x_1882_ = lean_array_propagate_mark(v_data_1875_, v___x_1881_);
v___x_1883_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v___x_1879_, v_data_1875_, v___x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(lean_object* v_m_1884_, lean_object* v_a_1885_, lean_object* v_b_1886_){
_start:
{
lean_object* v_size_1887_; lean_object* v_buckets_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1931_; 
v_size_1887_ = lean_ctor_get(v_m_1884_, 0);
v_buckets_1888_ = lean_ctor_get(v_m_1884_, 1);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_m_1884_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1890_ = v_m_1884_;
v_isShared_1891_ = v_isSharedCheck_1931_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_buckets_1888_);
lean_inc(v_size_1887_);
lean_dec(v_m_1884_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1931_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; uint64_t v___x_1893_; uint64_t v___x_1894_; uint64_t v___x_1895_; uint64_t v_fold_1896_; uint64_t v___x_1897_; uint64_t v___x_1898_; uint64_t v___x_1899_; size_t v___x_1900_; size_t v___x_1901_; size_t v___x_1902_; size_t v___x_1903_; size_t v___x_1904_; lean_object* v_bkt_1905_; uint8_t v___x_1906_; 
v___x_1892_ = lean_array_get_size(v_buckets_1888_);
v___x_1893_ = l_Lean_Expr_hash(v_a_1885_);
v___x_1894_ = 32ULL;
v___x_1895_ = lean_uint64_shift_right(v___x_1893_, v___x_1894_);
v_fold_1896_ = lean_uint64_xor(v___x_1893_, v___x_1895_);
v___x_1897_ = 16ULL;
v___x_1898_ = lean_uint64_shift_right(v_fold_1896_, v___x_1897_);
v___x_1899_ = lean_uint64_xor(v_fold_1896_, v___x_1898_);
v___x_1900_ = lean_uint64_to_usize(v___x_1899_);
v___x_1901_ = lean_usize_of_nat(v___x_1892_);
v___x_1902_ = ((size_t)1ULL);
v___x_1903_ = lean_usize_sub(v___x_1901_, v___x_1902_);
v___x_1904_ = lean_usize_land(v___x_1900_, v___x_1903_);
v_bkt_1905_ = lean_array_uget_borrowed(v_buckets_1888_, v___x_1904_);
v___x_1906_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_1885_, v_bkt_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v_size_x27_1908_; lean_object* v___x_1909_; lean_object* v_buckets_x27_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1907_ = lean_unsigned_to_nat(1u);
v_size_x27_1908_ = lean_nat_add(v_size_1887_, v___x_1907_);
lean_dec(v_size_1887_);
lean_inc(v_bkt_1905_);
v___x_1909_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1909_, 0, v_a_1885_);
lean_ctor_set(v___x_1909_, 1, v_b_1886_);
lean_ctor_set(v___x_1909_, 2, v_bkt_1905_);
v_buckets_x27_1910_ = lean_array_uset(v_buckets_1888_, v___x_1904_, v___x_1909_);
v___x_1911_ = lean_unsigned_to_nat(4u);
v___x_1912_ = lean_nat_mul(v_size_x27_1908_, v___x_1911_);
v___x_1913_ = lean_unsigned_to_nat(3u);
v___x_1914_ = lean_nat_div(v___x_1912_, v___x_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_array_get_size(v_buckets_x27_1910_);
v___x_1916_ = lean_nat_dec_le(v___x_1914_, v___x_1915_);
lean_dec(v___x_1914_);
if (v___x_1916_ == 0)
{
lean_object* v_val_1917_; lean_object* v___x_1919_; 
v_val_1917_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_buckets_x27_1910_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v_val_1917_);
lean_ctor_set(v___x_1890_, 0, v_size_x27_1908_);
v___x_1919_ = v___x_1890_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_size_x27_1908_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_val_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
else
{
lean_object* v___x_1922_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v_buckets_x27_1910_);
lean_ctor_set(v___x_1890_, 0, v_size_x27_1908_);
v___x_1922_ = v___x_1890_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_size_x27_1908_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_buckets_x27_1910_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
else
{
lean_object* v___x_1924_; lean_object* v_buckets_x27_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
lean_inc(v_bkt_1905_);
v___x_1924_ = lean_box(0);
v_buckets_x27_1925_ = lean_array_uset(v_buckets_1888_, v___x_1904_, v___x_1924_);
v___x_1926_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_1885_, v_b_1886_, v_bkt_1905_);
v___x_1927_ = lean_array_uset(v_buckets_x27_1925_, v___x_1904_, v___x_1926_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v___x_1927_);
v___x_1929_ = v___x_1890_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_size_1887_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(lean_object* v_g_1932_, lean_object* v_e_1933_, lean_object* v_a_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_a_1943_; lean_object* v___y_1949_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_st_ref_get(v_a_1934_);
v___x_1952_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v___x_1951_, v_e_1933_);
lean_dec(v___x_1951_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v___x_1953_; 
lean_inc_ref(v_g_1932_);
lean_inc(v___y_1940_);
lean_inc_ref(v___y_1939_);
lean_inc(v___y_1938_);
lean_inc_ref(v___y_1937_);
lean_inc(v___y_1936_);
lean_inc_ref(v___y_1935_);
lean_inc_ref(v_e_1933_);
v___x_1953_ = lean_apply_8(v_g_1932_, v_e_1933_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, lean_box(0));
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v_d_1956_; lean_object* v_b_1957_; lean_object* v___y_1958_; uint8_t v___x_1961_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v___x_1961_ = lean_unbox(v_a_1954_);
lean_dec(v_a_1954_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
lean_dec_ref(v_g_1932_);
v___x_1962_ = lean_box(0);
v_a_1943_ = v___x_1962_;
goto v___jp_1942_;
}
else
{
switch(lean_obj_tag(v_e_1933_))
{
case 7:
{
lean_object* v_binderType_1963_; lean_object* v_body_1964_; 
v_binderType_1963_ = lean_ctor_get(v_e_1933_, 1);
v_body_1964_ = lean_ctor_get(v_e_1933_, 2);
lean_inc_ref(v_body_1964_);
lean_inc_ref(v_binderType_1963_);
v_d_1956_ = v_binderType_1963_;
v_b_1957_ = v_body_1964_;
v___y_1958_ = v_a_1934_;
goto v___jp_1955_;
}
case 6:
{
lean_object* v_binderType_1965_; lean_object* v_body_1966_; 
v_binderType_1965_ = lean_ctor_get(v_e_1933_, 1);
v_body_1966_ = lean_ctor_get(v_e_1933_, 2);
lean_inc_ref(v_body_1966_);
lean_inc_ref(v_binderType_1965_);
v_d_1956_ = v_binderType_1965_;
v_b_1957_ = v_body_1966_;
v___y_1958_ = v_a_1934_;
goto v___jp_1955_;
}
case 8:
{
lean_object* v_type_1967_; lean_object* v_value_1968_; lean_object* v_body_1969_; lean_object* v___x_1970_; 
v_type_1967_ = lean_ctor_get(v_e_1933_, 1);
v_value_1968_ = lean_ctor_get(v_e_1933_, 2);
v_body_1969_ = lean_ctor_get(v_e_1933_, 3);
lean_inc_ref(v_type_1967_);
lean_inc_ref(v_g_1932_);
v___x_1970_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1932_, v_type_1967_, v_a_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1971_; 
lean_dec_ref_known(v___x_1970_, 1);
lean_inc_ref(v_value_1968_);
lean_inc_ref(v_g_1932_);
v___x_1971_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1932_, v_value_1968_, v_a_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v___x_1972_; 
lean_dec_ref_known(v___x_1971_, 1);
lean_inc_ref(v_body_1969_);
v___x_1972_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1932_, v_body_1969_, v_a_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
v___y_1949_ = v___x_1972_;
goto v___jp_1948_;
}
else
{
lean_dec_ref(v_g_1932_);
v___y_1949_ = v___x_1971_;
goto v___jp_1948_;
}
}
else
{
lean_dec_ref(v_g_1932_);
v___y_1949_ = v___x_1970_;
goto v___jp_1948_;
}
}
case 5:
{
lean_object* v_fn_1973_; lean_object* v_arg_1974_; lean_object* v___x_1975_; 
v_fn_1973_ = lean_ctor_get(v_e_1933_, 0);
v_arg_1974_ = lean_ctor_get(v_e_1933_, 1);
lean_inc_ref(v_fn_1973_);
lean_inc_ref(v_g_1932_);
v___x_1975_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1932_, v_fn_1973_, v_a_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v___x_1976_; 
lean_dec_ref_known(v___x_1975_, 1);
lean_inc_ref(v_arg_1974_);
v___x_1976_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1932_, v_arg_1974_, v_a_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
v___y_1949_ = v___x_1976_;
goto v___jp_1948_;
}
else
{
lean_dec_ref(v_g_1932_);
v___y_1949_ = v___x_1975_;
goto v___jp_1948_;
}
}
case 10:
{
lean_object* v_expr_1977_; lean_object* v___x_1978_; 
v_expr_1977_ = lean_ctor_get(v_e_1933_, 1);
lean_inc_ref(v_expr_1977_);
v___x_1978_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1932_, v_expr_1977_, v_a_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
v___y_1949_ = v___x_1978_;
goto v___jp_1948_;
}
case 11:
{
lean_object* v_struct_1979_; lean_object* v___x_1980_; 
v_struct_1979_ = lean_ctor_get(v_e_1933_, 2);
lean_inc_ref(v_struct_1979_);
v___x_1980_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1932_, v_struct_1979_, v_a_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
v___y_1949_ = v___x_1980_;
goto v___jp_1948_;
}
default: 
{
lean_object* v___x_1981_; 
lean_dec_ref(v_g_1932_);
v___x_1981_ = lean_box(0);
v_a_1943_ = v___x_1981_;
goto v___jp_1942_;
}
}
}
v___jp_1955_:
{
lean_object* v___x_1959_; 
lean_inc_ref(v_g_1932_);
v___x_1959_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1932_, v_d_1956_, v___y_1958_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v___x_1960_; 
lean_dec_ref_known(v___x_1959_, 1);
v___x_1960_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1932_, v_b_1957_, v___y_1958_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
v___y_1949_ = v___x_1960_;
goto v___jp_1948_;
}
else
{
lean_dec_ref(v_b_1957_);
lean_dec_ref(v_g_1932_);
v___y_1949_ = v___x_1959_;
goto v___jp_1948_;
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec_ref(v_e_1933_);
lean_dec_ref(v_g_1932_);
v_a_1982_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1953_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1953_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
else
{
lean_object* v_val_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec_ref(v_e_1933_);
lean_dec_ref(v_g_1932_);
v_val_1990_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1952_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_val_1990_);
lean_dec(v___x_1952_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 0);
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_val_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
v___jp_1942_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1944_ = lean_st_ref_take(v_a_1934_);
v___x_1945_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v___x_1944_, v_e_1933_, v_a_1943_);
v___x_1946_ = lean_st_ref_put(v_a_1934_, v___x_1945_);
v___x_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_a_1943_);
return v___x_1947_;
}
v___jp_1948_:
{
if (lean_obj_tag(v___y_1949_) == 0)
{
lean_object* v_a_1950_; 
v_a_1950_ = lean_ctor_get(v___y_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___y_1949_, 1);
v_a_1943_ = v_a_1950_;
goto v___jp_1942_;
}
else
{
lean_dec_ref(v_e_1933_);
return v___y_1949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(lean_object* v_g_1998_, lean_object* v_e_1999_, lean_object* v_a_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_1998_, v_e_1999_, v_a_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v_a_2000_);
return v_res_2008_;
}
}
static lean_object* _init_l_Lean_Expr_checkMaxShared___closed__0(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = lean_unsigned_to_nat(16u);
v___x_2011_ = lean_mk_array(v___x_2010_, v___x_2009_);
return v___x_2011_;
}
}
static lean_object* _init_l_Lean_Expr_checkMaxShared___closed__1(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__0, &l_Lean_Expr_checkMaxShared___closed__0_once, _init_l_Lean_Expr_checkMaxShared___closed__0);
v___x_2013_ = lean_unsigned_to_nat(0u);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v___x_2012_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared(lean_object* v_e_2015_, lean_object* v_msg_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v___f_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___f_2024_ = lean_alloc_closure((void*)(l_Lean_Expr_checkMaxShared___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2024_, 0, v_msg_2016_);
v___x_2025_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__1, &l_Lean_Expr_checkMaxShared___closed__1_once, _init_l_Lean_Expr_checkMaxShared___closed__1);
v___x_2026_ = lean_st_mk_ref(v___x_2025_);
v___x_2027_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v___f_2024_, v_e_2015_, v___x_2026_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2036_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2036_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2036_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2032_ = lean_st_ref_get(v___x_2026_);
lean_dec(v___x_2026_);
lean_dec(v___x_2032_);
if (v_isShared_2031_ == 0)
{
v___x_2034_ = v___x_2030_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2028_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
else
{
lean_dec(v___x_2026_);
return v___x_2027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___boxed(lean_object* v_e_2037_, lean_object* v_msg_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_Expr_checkMaxShared(v_e_2037_, v_msg_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(lean_object* v_00_u03b2_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_2048_, v_x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___boxed(lean_object* v_00_u03b2_2051_, lean_object* v_x_2052_, lean_object* v_x_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(v_00_u03b2_2051_, v_x_2052_, v_x_2053_);
lean_dec_ref(v_x_2053_);
lean_dec_ref(v_x_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_object* v_00_u03b2_2055_, lean_object* v_x_2056_, size_t v_x_2057_, lean_object* v_x_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_2056_, v_x_2057_, v_x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2060_, lean_object* v_x_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_){
_start:
{
size_t v_x_7973__boxed_2064_; lean_object* v_res_2065_; 
v_x_7973__boxed_2064_ = lean_unbox_usize(v_x_2062_);
lean_dec(v_x_2062_);
v_res_2065_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(v_00_u03b2_2060_, v_x_2061_, v_x_7973__boxed_2064_, v_x_2063_);
lean_dec_ref(v_x_2063_);
lean_dec_ref(v_x_2061_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(lean_object* v_00_u03b2_2066_, lean_object* v_m_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_2067_, v_a_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2070_, lean_object* v_m_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(v_00_u03b2_2070_, v_m_2071_, v_a_2072_);
lean_dec_ref(v_a_2072_);
lean_dec_ref(v_m_2071_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(lean_object* v_00_u03b2_2074_, lean_object* v_m_2075_, lean_object* v_a_2076_, lean_object* v_b_2077_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_m_2075_, v_a_2076_, v_b_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2079_, lean_object* v_keys_2080_, lean_object* v_vals_2081_, lean_object* v_heq_2082_, lean_object* v_i_2083_, lean_object* v_k_2084_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_2080_, v_vals_2081_, v_i_2083_, v_k_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2086_, lean_object* v_keys_2087_, lean_object* v_vals_2088_, lean_object* v_heq_2089_, lean_object* v_i_2090_, lean_object* v_k_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(v_00_u03b2_2086_, v_keys_2087_, v_vals_2088_, v_heq_2089_, v_i_2090_, v_k_2091_);
lean_dec_ref(v_k_2091_);
lean_dec_ref(v_vals_2088_);
lean_dec_ref(v_keys_2087_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2093_, lean_object* v_a_2094_, lean_object* v_x_2095_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_2094_, v_x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2097_, lean_object* v_a_2098_, lean_object* v_x_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(v_00_u03b2_2097_, v_a_2098_, v_x_2099_);
lean_dec(v_x_2099_);
lean_dec_ref(v_a_2098_);
return v_res_2100_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2101_, lean_object* v_a_2102_, lean_object* v_x_2103_){
_start:
{
uint8_t v___x_2104_; 
v___x_2104_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_2102_, v_x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2105_, lean_object* v_a_2106_, lean_object* v_x_2107_){
_start:
{
uint8_t v_res_2108_; lean_object* v_r_2109_; 
v_res_2108_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(v_00_u03b2_2105_, v_a_2106_, v_x_2107_);
lean_dec(v_x_2107_);
lean_dec_ref(v_a_2106_);
v_r_2109_ = lean_box(v_res_2108_);
return v_r_2109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2110_, lean_object* v_data_2111_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_data_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2113_, lean_object* v_a_2114_, lean_object* v_b_2115_, lean_object* v_x_2116_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_2114_, v_b_2115_, v_x_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_2118_, lean_object* v_i_2119_, lean_object* v_source_2120_, lean_object* v_target_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v_i_2119_, v_source_2120_, v_target_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9(lean_object* v_00_u03b2_2123_, lean_object* v_x_2124_, lean_object* v_x_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_x_2124_, v_x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared(lean_object* v_mvarId_2127_, lean_object* v_msg_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_MVarId_getDecl(v_mvarId_2127_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v_type_2138_; lean_object* v___x_2139_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v_type_2138_ = lean_ctor_get(v_a_2137_, 2);
lean_inc_ref(v_type_2138_);
lean_dec(v_a_2137_);
v___x_2139_ = l_Lean_Expr_checkMaxShared(v_type_2138_, v_msg_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
return v___x_2139_;
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec_ref(v_msg_2128_);
v_a_2140_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2136_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2136_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared___boxed(lean_object* v_mvarId_2148_, lean_object* v_msg_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_MVarId_checkMaxShared(v_mvarId_2148_, v_msg_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
return v_res_2157_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(lean_object* v_x_2158_){
_start:
{
if (lean_obj_tag(v_x_2158_) == 0)
{
uint8_t v___x_2159_; 
v___x_2159_ = 0;
return v___x_2159_;
}
else
{
lean_object* v_head_2160_; lean_object* v_tail_2161_; uint8_t v___x_2162_; 
v_head_2160_ = lean_ctor_get(v_x_2158_, 0);
v_tail_2161_ = lean_ctor_get(v_x_2158_, 1);
v___x_2162_ = l_Lean_Level_isAlreadyNormalizedCheap(v_head_2160_);
if (v___x_2162_ == 0)
{
uint8_t v___x_2163_; 
v___x_2163_ = 1;
return v___x_2163_;
}
else
{
v_x_2158_ = v_tail_2161_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0___boxed(lean_object* v_x_2165_){
_start:
{
uint8_t v_res_2166_; lean_object* v_r_2167_; 
v_res_2166_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_x_2165_);
lean_dec(v_x_2165_);
v_r_2167_ = lean_box(v_res_2166_);
return v_r_2167_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(lean_object* v_x_2168_){
_start:
{
switch(lean_obj_tag(v_x_2168_))
{
case 4:
{
lean_object* v_us_2169_; uint8_t v___x_2170_; 
v_us_2169_ = lean_ctor_get(v_x_2168_, 1);
v___x_2170_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_us_2169_);
return v___x_2170_;
}
case 3:
{
lean_object* v_u_2171_; uint8_t v___x_2172_; 
v_u_2171_ = lean_ctor_get(v_x_2168_, 0);
v___x_2172_ = l_Lean_Level_isAlreadyNormalizedCheap(v_u_2171_);
if (v___x_2172_ == 0)
{
uint8_t v___x_2173_; 
v___x_2173_ = 1;
return v___x_2173_;
}
else
{
uint8_t v___x_2174_; 
v___x_2174_ = 0;
return v___x_2174_;
}
}
default: 
{
uint8_t v___x_2175_; 
v___x_2175_ = 0;
return v___x_2175_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(lean_object* v_x_2176_){
_start:
{
uint8_t v_res_2177_; lean_object* v_r_2178_; 
v_res_2177_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(v_x_2176_);
lean_dec_ref(v_x_2176_);
v_r_2178_ = lean_box(v_res_2177_);
return v_r_2178_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(lean_object* v_e_2180_){
_start:
{
lean_object* v___f_2181_; lean_object* v___x_2182_; 
v___f_2181_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0));
v___x_2182_ = lean_find_expr(v___f_2181_, v_e_2180_);
if (lean_obj_tag(v___x_2182_) == 0)
{
uint8_t v___x_2183_; 
v___x_2183_ = 1;
return v___x_2183_;
}
else
{
uint8_t v___x_2184_; 
lean_dec_ref_known(v___x_2182_, 1);
v___x_2184_ = 0;
return v___x_2184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___boxed(lean_object* v_e_2185_){
_start:
{
uint8_t v_res_2186_; lean_object* v_r_2187_; 
v_res_2186_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_2185_);
lean_dec_ref(v_e_2185_);
v_r_2187_ = lean_box(v_res_2186_);
return v_r_2187_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
if (lean_obj_tag(v_a_2188_) == 0)
{
lean_object* v___x_2190_; 
v___x_2190_ = l_List_reverse___redArg(v_a_2189_);
return v___x_2190_;
}
else
{
lean_object* v_head_2191_; lean_object* v_tail_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2201_; 
v_head_2191_ = lean_ctor_get(v_a_2188_, 0);
v_tail_2192_ = lean_ctor_get(v_a_2188_, 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_a_2188_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2194_ = v_a_2188_;
v_isShared_2195_ = v_isSharedCheck_2201_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_tail_2192_);
lean_inc(v_head_2191_);
lean_dec(v_a_2188_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2201_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2196_ = l_Lean_Level_normalize(v_head_2191_);
lean_dec(v_head_2191_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 1, v_a_2189_);
lean_ctor_set(v___x_2194_, 0, v___x_2196_);
v___x_2198_ = v___x_2194_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_a_2189_);
v___x_2198_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
v_a_2188_ = v_tail_2192_;
v_a_2189_ = v___x_2198_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0(lean_object* v_e_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v___y_2209_; lean_object* v___y_2213_; 
switch(lean_obj_tag(v_e_2204_))
{
case 3:
{
lean_object* v_u_2216_; lean_object* v___x_2217_; size_t v___x_2218_; size_t v___x_2219_; uint8_t v___x_2220_; 
v_u_2216_ = lean_ctor_get(v_e_2204_, 0);
v___x_2217_ = l_Lean_Level_normalize(v_u_2216_);
v___x_2218_ = lean_ptr_addr(v_u_2216_);
v___x_2219_ = lean_ptr_addr(v___x_2217_);
v___x_2220_ = lean_usize_dec_eq(v___x_2218_, v___x_2219_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; 
lean_dec_ref_known(v_e_2204_, 1);
v___x_2221_ = l_Lean_Expr_sort___override(v___x_2217_);
v___y_2209_ = v___x_2221_;
goto v___jp_2208_;
}
else
{
lean_dec(v___x_2217_);
v___y_2209_ = v_e_2204_;
goto v___jp_2208_;
}
}
case 4:
{
lean_object* v_declName_2222_; lean_object* v_us_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; 
v_declName_2222_ = lean_ctor_get(v_e_2204_, 0);
v_us_2223_ = lean_ctor_get(v_e_2204_, 1);
v___x_2224_ = lean_box(0);
lean_inc(v_us_2223_);
v___x_2225_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(v_us_2223_, v___x_2224_);
v___x_2226_ = l_ptrEqList___redArg(v_us_2223_, v___x_2225_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2227_; 
lean_inc(v_declName_2222_);
lean_dec_ref_known(v_e_2204_, 2);
v___x_2227_ = l_Lean_Expr_const___override(v_declName_2222_, v___x_2225_);
v___y_2213_ = v___x_2227_;
goto v___jp_2212_;
}
else
{
lean_dec(v___x_2225_);
v___y_2213_ = v_e_2204_;
goto v___jp_2212_;
}
}
default: 
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec_ref(v_e_2204_);
v___x_2228_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___lam__0___closed__0));
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
return v___x_2229_;
}
}
v___jp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___y_2209_);
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
return v___x_2211_;
}
v___jp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___y_2213_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed(lean_object* v_e_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_Meta_Sym_normalizeLevels___lam__0(v_e_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1(lean_object* v_e_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v_e_2235_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed(lean_object* v_e_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_Meta_Sym_normalizeLevels___lam__1(v_e_2241_, v___y_2242_, v___y_2243_);
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
lean_object* v___y_2280_; lean_object* v___y_2290_; lean_object* v___y_2291_; uint8_t v___y_2292_; uint8_t v___y_2293_; uint16_t v___y_2294_; lean_object* v___y_2295_; lean_object* v_toCold_2300_; lean_object* v_currRecDepth_2301_; lean_object* v_ref_2302_; uint16_t v_optionFlags_2303_; uint8_t v_suppressElabErrors_2304_; uint8_t v_isRecordingDeps_2305_; lean_object* v_maxRecDepth_2306_; lean_object* v_cancelTk_x3f_2307_; 
v_toCold_2300_ = lean_ctor_get(v___y_2276_, 0);
v_currRecDepth_2301_ = lean_ctor_get(v___y_2276_, 1);
v_ref_2302_ = lean_ctor_get(v___y_2276_, 2);
v_optionFlags_2303_ = lean_ctor_get_uint16(v___y_2276_, sizeof(void*)*3);
v_suppressElabErrors_2304_ = lean_ctor_get_uint8(v___y_2276_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2305_ = lean_ctor_get_uint8(v___y_2276_, sizeof(void*)*3 + 3);
v_maxRecDepth_2306_ = lean_ctor_get(v_toCold_2300_, 3);
v_cancelTk_x3f_2307_ = lean_ctor_get(v_toCold_2300_, 10);
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
lean_dec_ref(v_x_2274_);
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
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2296_ = lean_unsigned_to_nat(1u);
v___x_2297_ = lean_nat_add(v___y_2291_, v___x_2296_);
lean_inc_ref(v___y_2295_);
v___x_2298_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2298_, 0, v___y_2295_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
lean_ctor_set(v___x_2298_, 2, v___y_2290_);
lean_ctor_set_uint16(v___x_2298_, sizeof(void*)*3, v___y_2294_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*3 + 2, v___y_2293_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*3 + 3, v___y_2292_);
lean_inc(v___y_2277_);
lean_inc(v___y_2275_);
v___x_2299_ = lean_apply_4(v_x_2274_, v___y_2275_, v___x_2298_, v___y_2277_, lean_box(0));
v___y_2280_ = v___x_2299_;
goto v___jp_2279_;
}
v___jp_2308_:
{
lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = lean_nat_dec_eq(v_maxRecDepth_2306_, v___x_2309_);
if (v___x_2310_ == 0)
{
uint8_t v___x_2311_; 
v___x_2311_ = lean_nat_dec_eq(v_currRecDepth_2301_, v_maxRecDepth_2306_);
if (v___x_2311_ == 0)
{
lean_inc(v_ref_2302_);
v___y_2290_ = v_ref_2302_;
v___y_2291_ = v_currRecDepth_2301_;
v___y_2292_ = v_isRecordingDeps_2305_;
v___y_2293_ = v_suppressElabErrors_2304_;
v___y_2294_ = v_optionFlags_2303_;
v___y_2295_ = v_toCold_2300_;
goto v___jp_2289_;
}
else
{
lean_object* v___x_2312_; 
lean_dec_ref(v_x_2274_);
lean_inc(v_ref_2302_);
v___x_2312_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2302_);
v___y_2280_ = v___x_2312_;
goto v___jp_2279_;
}
}
else
{
lean_inc(v_ref_2302_);
v___y_2290_ = v_ref_2302_;
v___y_2291_ = v_currRecDepth_2301_;
v___y_2292_ = v_isRecordingDeps_2305_;
v___y_2293_ = v_suppressElabErrors_2304_;
v___y_2294_ = v_optionFlags_2303_;
v___y_2295_ = v_toCold_2300_;
goto v___jp_2289_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_a_2469_, lean_object* v_x_2470_){
_start:
{
if (lean_obj_tag(v_x_2470_) == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_box(0);
return v___x_2471_;
}
else
{
lean_object* v_key_2472_; lean_object* v_value_2473_; lean_object* v_tail_2474_; uint8_t v___x_2475_; 
v_key_2472_ = lean_ctor_get(v_x_2470_, 0);
v_value_2473_ = lean_ctor_get(v_x_2470_, 1);
v_tail_2474_ = lean_ctor_get(v_x_2470_, 2);
v___x_2475_ = l_Lean_ExprStructEq_beq(v_key_2472_, v_a_2469_);
if (v___x_2475_ == 0)
{
v_x_2470_ = v_tail_2474_;
goto _start;
}
else
{
lean_object* v___x_2477_; 
lean_inc(v_value_2473_);
v___x_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2477_, 0, v_value_2473_);
return v___x_2477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg___boxed(lean_object* v_a_2478_, lean_object* v_x_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(v_a_2478_, v_x_2479_);
lean_dec(v_x_2479_);
lean_dec_ref(v_a_2478_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(lean_object* v_m_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_buckets_2483_; lean_object* v___x_2484_; uint64_t v___x_2485_; uint64_t v___x_2486_; uint64_t v___x_2487_; uint64_t v_fold_2488_; uint64_t v___x_2489_; uint64_t v___x_2490_; uint64_t v___x_2491_; size_t v___x_2492_; size_t v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v_buckets_2483_ = lean_ctor_get(v_m_2481_, 1);
v___x_2484_ = lean_array_get_size(v_buckets_2483_);
v___x_2485_ = l_Lean_ExprStructEq_hash(v_a_2482_);
v___x_2486_ = 32ULL;
v___x_2487_ = lean_uint64_shift_right(v___x_2485_, v___x_2486_);
v_fold_2488_ = lean_uint64_xor(v___x_2485_, v___x_2487_);
v___x_2489_ = 16ULL;
v___x_2490_ = lean_uint64_shift_right(v_fold_2488_, v___x_2489_);
v___x_2491_ = lean_uint64_xor(v_fold_2488_, v___x_2490_);
v___x_2492_ = lean_uint64_to_usize(v___x_2491_);
v___x_2493_ = lean_usize_of_nat(v___x_2484_);
v___x_2494_ = ((size_t)1ULL);
v___x_2495_ = lean_usize_sub(v___x_2493_, v___x_2494_);
v___x_2496_ = lean_usize_land(v___x_2492_, v___x_2495_);
v___x_2497_ = lean_array_uget_borrowed(v_buckets_2483_, v___x_2496_);
v___x_2498_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(v_a_2482_, v___x_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_m_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(v_m_2499_, v_a_2500_);
lean_dec_ref(v_a_2500_);
lean_dec_ref(v_m_2499_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2502_, lean_object* v_x_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = lean_apply_1(v_x_2503_, lean_box(0));
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2509_, lean_object* v_x_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(v_00_u03b1_2509_, v_x_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object* v_pre_2518_, lean_object* v_post_2519_, size_t v_sz_2520_, size_t v_i_2521_, lean_object* v_bs_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(lean_object* v_pre_2546_, lean_object* v_post_2547_, lean_object* v_x_2548_, lean_object* v_x_2549_, lean_object* v_x_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
if (lean_obj_tag(v_x_2548_) == 5)
{
lean_object* v_fn_2555_; lean_object* v_arg_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v_fn_2555_ = lean_ctor_get(v_x_2548_, 0);
lean_inc_ref(v_fn_2555_);
v_arg_2556_ = lean_ctor_get(v_x_2548_, 1);
lean_inc_ref(v_arg_2556_);
lean_dec_ref_known(v_x_2548_, 2);
v___x_2557_ = lean_array_set(v_x_2549_, v_x_2550_, v_arg_2556_);
v___x_2558_ = lean_unsigned_to_nat(1u);
v___x_2559_ = lean_nat_sub(v_x_2550_, v___x_2558_);
lean_dec(v_x_2550_);
v_x_2548_ = v_fn_2555_;
v_x_2549_ = v___x_2557_;
v_x_2550_ = v___x_2559_;
goto _start;
}
else
{
lean_object* v___x_2561_; 
lean_dec(v_x_2550_);
lean_inc_ref(v_post_2547_);
lean_inc_ref(v_pre_2546_);
v___x_2561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2546_, v_post_2547_, v_x_2548_, v___y_2551_, v___y_2552_, v___y_2553_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; size_t v_sz_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v_sz_2563_ = lean_array_size(v_x_2549_);
v___x_2564_ = ((size_t)0ULL);
lean_inc_ref(v_post_2547_);
lean_inc_ref(v_pre_2546_);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_2546_, v_post_2547_, v_sz_2563_, v___x_2564_, v_x_2549_, v___y_2551_, v___y_2552_, v___y_2553_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = l_Lean_mkAppN(v_a_2562_, v_a_2566_);
lean_dec(v_a_2566_);
v___x_2568_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2546_, v_post_2547_, v___x_2567_, v___y_2551_, v___y_2552_, v___y_2553_);
return v___x_2568_;
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec(v_a_2562_);
lean_dec_ref(v_post_2547_);
lean_dec_ref(v_pre_2546_);
v_a_2569_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2565_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2565_);
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
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_dec_ref(v_x_2549_);
lean_dec_ref(v_post_2547_);
lean_dec_ref(v_pre_2546_);
return v___x_2561_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object* v___x_2577_, lean_object* v_pre_2578_, lean_object* v_e_2579_, lean_object* v_post_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_Core_checkSystem(v___x_2577_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v___x_2586_; 
lean_dec_ref_known(v___x_2585_, 1);
lean_inc_ref(v_pre_2578_);
lean_inc(v___y_2583_);
lean_inc_ref(v___y_2582_);
lean_inc_ref(v_e_2579_);
v___x_2586_ = lean_apply_4(v_pre_2578_, v_e_2579_, v___y_2582_, v___y_2583_, lean_box(0));
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2702_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2702_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2702_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___y_2592_; 
switch(lean_obj_tag(v_a_2587_))
{
case 0:
{
lean_object* v_e_2692_; lean_object* v___x_2694_; 
lean_dec_ref(v_post_2580_);
lean_dec_ref(v_e_2579_);
lean_dec_ref(v_pre_2578_);
v_e_2692_ = lean_ctor_get(v_a_2587_, 0);
lean_inc_ref(v_e_2692_);
lean_dec_ref_known(v_a_2587_, 1);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v_e_2692_);
v___x_2694_ = v___x_2589_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_e_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
case 1:
{
lean_object* v_e_2696_; lean_object* v___x_2697_; 
lean_del_object(v___x_2589_);
lean_dec_ref(v_e_2579_);
v_e_2696_ = lean_ctor_get(v_a_2587_, 0);
lean_inc_ref(v_e_2696_);
lean_dec_ref_known(v_a_2587_, 1);
lean_inc_ref(v_post_2580_);
lean_inc_ref(v_pre_2578_);
v___x_2697_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2578_, v_post_2580_, v_e_2696_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2699_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2699_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v_a_2698_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2699_;
}
else
{
lean_dec_ref(v_post_2580_);
lean_dec_ref(v_pre_2578_);
return v___x_2697_;
}
}
default: 
{
lean_object* v_e_x3f_2700_; 
lean_del_object(v___x_2589_);
v_e_x3f_2700_ = lean_ctor_get(v_a_2587_, 0);
lean_inc(v_e_x3f_2700_);
lean_dec_ref_known(v_a_2587_, 1);
if (lean_obj_tag(v_e_x3f_2700_) == 0)
{
v___y_2592_ = v_e_2579_;
goto v___jp_2591_;
}
else
{
lean_object* v_val_2701_; 
lean_dec_ref(v_e_2579_);
v_val_2701_ = lean_ctor_get(v_e_x3f_2700_, 0);
lean_inc(v_val_2701_);
lean_dec_ref_known(v_e_x3f_2700_, 1);
v___y_2592_ = v_val_2701_;
goto v___jp_2591_;
}
}
}
v___jp_2591_:
{
switch(lean_obj_tag(v___y_2592_))
{
case 7:
{
lean_object* v_binderName_2593_; lean_object* v_binderType_2594_; lean_object* v_body_2595_; uint8_t v_binderInfo_2596_; lean_object* v___x_2597_; 
v_binderName_2593_ = lean_ctor_get(v___y_2592_, 0);
v_binderType_2594_ = lean_ctor_get(v___y_2592_, 1);
v_body_2595_ = lean_ctor_get(v___y_2592_, 2);
v_binderInfo_2596_ = lean_ctor_get_uint8(v___y_2592_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2594_);
lean_inc_ref(v_post_2580_);
lean_inc_ref(v_pre_2578_);
v___x_2597_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2578_, v_post_2580_, v_binderType_2594_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2599_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
lean_inc_ref(v_body_2595_);
lean_inc_ref(v_post_2580_);
lean_inc_ref(v_pre_2578_);
v___x_2599_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2578_, v_post_2580_, v_body_2595_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; size_t v___x_2601_; size_t v___x_2602_; uint8_t v___x_2603_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v___x_2601_ = lean_ptr_addr(v_binderType_2594_);
v___x_2602_ = lean_ptr_addr(v_a_2598_);
v___x_2603_ = lean_usize_dec_eq(v___x_2601_, v___x_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
lean_inc(v_binderName_2593_);
lean_dec_ref_known(v___y_2592_, 3);
v___x_2604_ = l_Lean_Expr_forallE___override(v_binderName_2593_, v_a_2598_, v_a_2600_, v_binderInfo_2596_);
v___x_2605_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___x_2604_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2605_;
}
else
{
size_t v___x_2606_; size_t v___x_2607_; uint8_t v___x_2608_; 
v___x_2606_ = lean_ptr_addr(v_body_2595_);
v___x_2607_ = lean_ptr_addr(v_a_2600_);
v___x_2608_ = lean_usize_dec_eq(v___x_2606_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_inc(v_binderName_2593_);
lean_dec_ref_known(v___y_2592_, 3);
v___x_2609_ = l_Lean_Expr_forallE___override(v_binderName_2593_, v_a_2598_, v_a_2600_, v_binderInfo_2596_);
v___x_2610_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___x_2609_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2610_;
}
else
{
uint8_t v___x_2611_; 
v___x_2611_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2596_, v_binderInfo_2596_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
lean_inc(v_binderName_2593_);
lean_dec_ref_known(v___y_2592_, 3);
v___x_2612_ = l_Lean_Expr_forallE___override(v_binderName_2593_, v_a_2598_, v_a_2600_, v_binderInfo_2596_);
v___x_2613_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___x_2612_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2613_;
}
else
{
lean_object* v___x_2614_; 
lean_dec(v_a_2600_);
lean_dec(v_a_2598_);
v___x_2614_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___y_2592_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2614_;
}
}
}
}
else
{
lean_dec(v_a_2598_);
lean_dec_ref_known(v___y_2592_, 3);
lean_dec_ref(v_post_2580_);
lean_dec_ref(v_pre_2578_);
return v___x_2599_;
}
}
else
{
lean_dec_ref_known(v___y_2592_, 3);
lean_dec_ref(v_post_2580_);
lean_dec_ref(v_pre_2578_);
return v___x_2597_;
}
}
case 6:
{
lean_object* v_binderName_2615_; lean_object* v_binderType_2616_; lean_object* v_body_2617_; uint8_t v_binderInfo_2618_; lean_object* v___x_2619_; 
v_binderName_2615_ = lean_ctor_get(v___y_2592_, 0);
v_binderType_2616_ = lean_ctor_get(v___y_2592_, 1);
v_body_2617_ = lean_ctor_get(v___y_2592_, 2);
v_binderInfo_2618_ = lean_ctor_get_uint8(v___y_2592_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2616_);
lean_inc_ref(v_post_2580_);
lean_inc_ref(v_pre_2578_);
v___x_2619_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2578_, v_post_2580_, v_binderType_2616_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2621_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v___x_2619_, 1);
lean_inc_ref(v_body_2617_);
lean_inc_ref(v_post_2580_);
lean_inc_ref(v_pre_2578_);
v___x_2621_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2578_, v_post_2580_, v_body_2617_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; size_t v___x_2623_; size_t v___x_2624_; uint8_t v___x_2625_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v___x_2623_ = lean_ptr_addr(v_binderType_2616_);
v___x_2624_ = lean_ptr_addr(v_a_2620_);
v___x_2625_ = lean_usize_dec_eq(v___x_2623_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_inc(v_binderName_2615_);
lean_dec_ref_known(v___y_2592_, 3);
v___x_2626_ = l_Lean_Expr_lam___override(v_binderName_2615_, v_a_2620_, v_a_2622_, v_binderInfo_2618_);
v___x_2627_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___x_2626_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2627_;
}
else
{
size_t v___x_2628_; size_t v___x_2629_; uint8_t v___x_2630_; 
v___x_2628_ = lean_ptr_addr(v_body_2617_);
v___x_2629_ = lean_ptr_addr(v_a_2622_);
v___x_2630_ = lean_usize_dec_eq(v___x_2628_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_inc(v_binderName_2615_);
lean_dec_ref_known(v___y_2592_, 3);
v___x_2631_ = l_Lean_Expr_lam___override(v_binderName_2615_, v_a_2620_, v_a_2622_, v_binderInfo_2618_);
v___x_2632_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___x_2631_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2632_;
}
else
{
uint8_t v___x_2633_; 
v___x_2633_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2618_, v_binderInfo_2618_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_inc(v_binderName_2615_);
lean_dec_ref_known(v___y_2592_, 3);
v___x_2634_ = l_Lean_Expr_lam___override(v_binderName_2615_, v_a_2620_, v_a_2622_, v_binderInfo_2618_);
v___x_2635_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___x_2634_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2635_;
}
else
{
lean_object* v___x_2636_; 
lean_dec(v_a_2622_);
lean_dec(v_a_2620_);
v___x_2636_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___y_2592_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2636_;
}
}
}
}
else
{
lean_dec(v_a_2620_);
lean_dec_ref_known(v___y_2592_, 3);
lean_dec_ref(v_post_2580_);
lean_dec_ref(v_pre_2578_);
return v___x_2621_;
}
}
else
{
lean_dec_ref_known(v___y_2592_, 3);
lean_dec_ref(v_post_2580_);
lean_dec_ref(v_pre_2578_);
return v___x_2619_;
}
}
case 8:
{
lean_object* v_declName_2637_; lean_object* v_type_2638_; lean_object* v_value_2639_; lean_object* v_body_2640_; uint8_t v_nondep_2641_; lean_object* v___x_2642_; 
v_declName_2637_ = lean_ctor_get(v___y_2592_, 0);
v_type_2638_ = lean_ctor_get(v___y_2592_, 1);
v_value_2639_ = lean_ctor_get(v___y_2592_, 2);
v_body_2640_ = lean_ctor_get(v___y_2592_, 3);
v_nondep_2641_ = lean_ctor_get_uint8(v___y_2592_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2638_);
lean_inc_ref(v_post_2580_);
lean_inc_ref(v_pre_2578_);
v___x_2642_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2578_, v_post_2580_, v_type_2638_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2644_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
lean_inc_ref(v_value_2639_);
lean_inc_ref(v_post_2580_);
lean_inc_ref(v_pre_2578_);
v___x_2644_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2578_, v_post_2580_, v_value_2639_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2646_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
lean_inc_ref(v_body_2640_);
lean_inc_ref(v_post_2580_);
lean_inc_ref(v_pre_2578_);
v___x_2646_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2578_, v_post_2580_, v_body_2640_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; size_t v___x_2648_; size_t v___x_2649_; uint8_t v___x_2650_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v___x_2648_ = lean_ptr_addr(v_type_2638_);
v___x_2649_ = lean_ptr_addr(v_a_2643_);
v___x_2650_ = lean_usize_dec_eq(v___x_2648_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_inc(v_declName_2637_);
lean_dec_ref_known(v___y_2592_, 4);
v___x_2651_ = l_Lean_Expr_letE___override(v_declName_2637_, v_a_2643_, v_a_2645_, v_a_2647_, v_nondep_2641_);
v___x_2652_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___x_2651_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2652_;
}
else
{
size_t v___x_2653_; size_t v___x_2654_; uint8_t v___x_2655_; 
v___x_2653_ = lean_ptr_addr(v_value_2639_);
v___x_2654_ = lean_ptr_addr(v_a_2645_);
v___x_2655_ = lean_usize_dec_eq(v___x_2653_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_inc(v_declName_2637_);
lean_dec_ref_known(v___y_2592_, 4);
v___x_2656_ = l_Lean_Expr_letE___override(v_declName_2637_, v_a_2643_, v_a_2645_, v_a_2647_, v_nondep_2641_);
v___x_2657_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___x_2656_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2657_;
}
else
{
size_t v___x_2658_; size_t v___x_2659_; uint8_t v___x_2660_; 
v___x_2658_ = lean_ptr_addr(v_body_2640_);
v___x_2659_ = lean_ptr_addr(v_a_2647_);
v___x_2660_ = lean_usize_dec_eq(v___x_2658_, v___x_2659_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_inc(v_declName_2637_);
lean_dec_ref_known(v___y_2592_, 4);
v___x_2661_ = l_Lean_Expr_letE___override(v_declName_2637_, v_a_2643_, v_a_2645_, v_a_2647_, v_nondep_2641_);
v___x_2662_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___x_2661_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2662_;
}
else
{
lean_object* v___x_2663_; 
lean_dec(v_a_2647_);
lean_dec(v_a_2645_);
lean_dec(v_a_2643_);
v___x_2663_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___y_2592_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2663_;
}
}
}
}
else
{
lean_dec(v_a_2645_);
lean_dec(v_a_2643_);
lean_dec_ref_known(v___y_2592_, 4);
lean_dec_ref(v_post_2580_);
lean_dec_ref(v_pre_2578_);
return v___x_2646_;
}
}
else
{
lean_dec(v_a_2643_);
lean_dec_ref_known(v___y_2592_, 4);
lean_dec_ref(v_post_2580_);
lean_dec_ref(v_pre_2578_);
return v___x_2644_;
}
}
else
{
lean_dec_ref_known(v___y_2592_, 4);
lean_dec_ref(v_post_2580_);
lean_dec_ref(v_pre_2578_);
return v___x_2642_;
}
}
case 5:
{
lean_object* v_dummy_2664_; lean_object* v_nargs_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_dummy_2664_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___closed__0);
v_nargs_2665_ = l_Lean_Expr_getAppNumArgs(v___y_2592_);
lean_inc(v_nargs_2665_);
v___x_2666_ = lean_mk_array(v_nargs_2665_, v_dummy_2664_);
v___x_2667_ = lean_unsigned_to_nat(1u);
v___x_2668_ = lean_nat_sub(v_nargs_2665_, v___x_2667_);
lean_dec(v_nargs_2665_);
v___x_2669_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_pre_2578_, v_post_2580_, v___y_2592_, v___x_2666_, v___x_2668_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2669_;
}
case 10:
{
lean_object* v_data_2670_; lean_object* v_expr_2671_; lean_object* v___x_2672_; 
v_data_2670_ = lean_ctor_get(v___y_2592_, 0);
v_expr_2671_ = lean_ctor_get(v___y_2592_, 1);
lean_inc_ref(v_expr_2671_);
lean_inc_ref(v_post_2580_);
lean_inc_ref(v_pre_2578_);
v___x_2672_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2578_, v_post_2580_, v_expr_2671_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; size_t v___x_2674_; size_t v___x_2675_; uint8_t v___x_2676_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2674_ = lean_ptr_addr(v_expr_2671_);
v___x_2675_ = lean_ptr_addr(v_a_2673_);
v___x_2676_ = lean_usize_dec_eq(v___x_2674_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_inc(v_data_2670_);
lean_dec_ref_known(v___y_2592_, 2);
v___x_2677_ = l_Lean_Expr_mdata___override(v_data_2670_, v_a_2673_);
v___x_2678_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___x_2677_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2678_;
}
else
{
lean_object* v___x_2679_; 
lean_dec(v_a_2673_);
v___x_2679_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___y_2592_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2679_;
}
}
else
{
lean_dec_ref_known(v___y_2592_, 2);
lean_dec_ref(v_post_2580_);
lean_dec_ref(v_pre_2578_);
return v___x_2672_;
}
}
case 11:
{
lean_object* v_typeName_2680_; lean_object* v_idx_2681_; lean_object* v_struct_2682_; lean_object* v___x_2683_; 
v_typeName_2680_ = lean_ctor_get(v___y_2592_, 0);
v_idx_2681_ = lean_ctor_get(v___y_2592_, 1);
v_struct_2682_ = lean_ctor_get(v___y_2592_, 2);
lean_inc_ref(v_struct_2682_);
lean_inc_ref(v_post_2580_);
lean_inc_ref(v_pre_2578_);
v___x_2683_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2578_, v_post_2580_, v_struct_2682_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; size_t v___x_2685_; size_t v___x_2686_; uint8_t v___x_2687_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v___x_2683_, 1);
v___x_2685_ = lean_ptr_addr(v_struct_2682_);
v___x_2686_ = lean_ptr_addr(v_a_2684_);
v___x_2687_ = lean_usize_dec_eq(v___x_2685_, v___x_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
lean_inc(v_idx_2681_);
lean_inc(v_typeName_2680_);
lean_dec_ref_known(v___y_2592_, 3);
v___x_2688_ = l_Lean_Expr_proj___override(v_typeName_2680_, v_idx_2681_, v_a_2684_);
v___x_2689_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___x_2688_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2689_;
}
else
{
lean_object* v___x_2690_; 
lean_dec(v_a_2684_);
v___x_2690_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___y_2592_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2690_;
}
}
else
{
lean_dec_ref_known(v___y_2592_, 3);
lean_dec_ref(v_post_2580_);
lean_dec_ref(v_pre_2578_);
return v___x_2683_;
}
}
default: 
{
lean_object* v___x_2691_; 
v___x_2691_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2578_, v_post_2580_, v___y_2592_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2691_;
}
}
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec_ref(v_post_2580_);
lean_dec_ref(v_e_2579_);
lean_dec_ref(v_pre_2578_);
v_a_2703_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2586_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2586_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
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
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref(v_post_2580_);
lean_dec_ref(v_e_2579_);
lean_dec_ref(v_pre_2578_);
v_a_2711_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2585_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2585_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object* v___x_2719_, lean_object* v_pre_2720_, lean_object* v_e_2721_, lean_object* v_post_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(v___x_2719_, v_pre_2720_, v_e_2721_, v_post_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(lean_object* v_pre_2728_, lean_object* v_post_2729_, lean_object* v_e_2730_, lean_object* v_a_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_inc(v_a_2731_);
v___x_2735_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2735_, 0, lean_box(0));
lean_closure_set(v___x_2735_, 1, lean_box(0));
lean_closure_set(v___x_2735_, 2, v_a_2731_);
v___x_2736_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___x_2735_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2768_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2739_ = v___x_2736_;
v_isShared_2740_ = v_isSharedCheck_2768_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2768_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(v_a_2737_, v_e_2730_);
lean_dec(v_a_2737_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v___x_2742_; lean_object* v___f_2743_; lean_object* v___x_2744_; 
lean_del_object(v___x_2739_);
v___x_2742_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___closed__0));
lean_inc_ref(v_e_2730_);
v___f_2743_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed), 8, 4);
lean_closure_set(v___f_2743_, 0, v___x_2742_);
lean_closure_set(v___f_2743_, 1, v_pre_2728_);
lean_closure_set(v___f_2743_, 2, v_e_2730_);
lean_closure_set(v___f_2743_, 3, v_post_2729_);
v___x_2744_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v___f_2743_, v_a_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___f_2746_; lean_object* v___x_2747_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc_n(v_a_2745_, 2);
lean_dec_ref_known(v___x_2744_, 1);
lean_inc(v_a_2731_);
v___f_2746_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2746_, 0, v_a_2731_);
lean_closure_set(v___f_2746_, 1, v_e_2730_);
lean_closure_set(v___f_2746_, 2, v_a_2745_);
v___x_2747_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___f_2746_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2754_ == 0)
{
lean_object* v_unused_2755_; 
v_unused_2755_ = lean_ctor_get(v___x_2747_, 0);
lean_dec(v_unused_2755_);
v___x_2749_ = v___x_2747_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_dec(v___x_2747_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v_a_2745_);
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2745_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec(v_a_2745_);
v_a_2756_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2747_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2747_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
else
{
lean_dec_ref(v_e_2730_);
return v___x_2744_;
}
}
else
{
lean_object* v_val_2764_; lean_object* v___x_2766_; 
lean_dec_ref(v_e_2730_);
lean_dec_ref(v_post_2729_);
lean_dec_ref(v_pre_2728_);
v_val_2764_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v___x_2741_, 1);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 0, v_val_2764_);
v___x_2766_ = v___x_2739_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_val_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec_ref(v_e_2730_);
lean_dec_ref(v_post_2729_);
lean_dec_ref(v_pre_2728_);
v_a_2769_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2736_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2736_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(lean_object* v_pre_2777_, lean_object* v_post_2778_, lean_object* v_e_2779_, lean_object* v_a_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; 
lean_inc_ref(v_post_2778_);
lean_inc(v___y_2782_);
lean_inc_ref(v___y_2781_);
lean_inc_ref(v_e_2779_);
v___x_2784_ = lean_apply_4(v_post_2778_, v_e_2779_, v___y_2781_, v___y_2782_, lean_box(0));
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2803_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2803_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2803_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
switch(lean_obj_tag(v_a_2785_))
{
case 0:
{
lean_object* v_e_2789_; lean_object* v___x_2791_; 
lean_dec_ref(v_e_2779_);
lean_dec_ref(v_post_2778_);
lean_dec_ref(v_pre_2777_);
v_e_2789_ = lean_ctor_get(v_a_2785_, 0);
lean_inc_ref(v_e_2789_);
lean_dec_ref_known(v_a_2785_, 1);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v_e_2789_);
v___x_2791_ = v___x_2787_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_e_2789_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
case 1:
{
lean_object* v_e_2793_; lean_object* v___x_2794_; 
lean_del_object(v___x_2787_);
lean_dec_ref(v_e_2779_);
v_e_2793_ = lean_ctor_get(v_a_2785_, 0);
lean_inc_ref(v_e_2793_);
lean_dec_ref_known(v_a_2785_, 1);
v___x_2794_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2777_, v_post_2778_, v_e_2793_, v_a_2780_, v___y_2781_, v___y_2782_);
return v___x_2794_;
}
default: 
{
lean_object* v_e_x3f_2795_; 
lean_dec_ref(v_post_2778_);
lean_dec_ref(v_pre_2777_);
v_e_x3f_2795_ = lean_ctor_get(v_a_2785_, 0);
lean_inc(v_e_x3f_2795_);
lean_dec_ref_known(v_a_2785_, 1);
if (lean_obj_tag(v_e_x3f_2795_) == 0)
{
lean_object* v___x_2797_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v_e_2779_);
v___x_2797_ = v___x_2787_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_e_2779_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
else
{
lean_object* v_val_2799_; lean_object* v___x_2801_; 
lean_dec_ref(v_e_2779_);
v_val_2799_ = lean_ctor_get(v_e_x3f_2795_, 0);
lean_inc(v_val_2799_);
lean_dec_ref_known(v_e_x3f_2795_, 1);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v_val_2799_);
v___x_2801_ = v___x_2787_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_val_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec_ref(v_e_2779_);
lean_dec_ref(v_post_2778_);
lean_dec_ref(v_pre_2777_);
v_a_2804_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2784_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2784_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_2812_, lean_object* v_post_2813_, lean_object* v_e_2814_, lean_object* v_a_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_2812_, v_post_2813_, v_e_2814_, v_a_2815_, v___y_2816_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v_a_2815_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_2820_, lean_object* v_post_2821_, lean_object* v_sz_2822_, lean_object* v_i_2823_, lean_object* v_bs_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
size_t v_sz_boxed_2829_; size_t v_i_boxed_2830_; lean_object* v_res_2831_; 
v_sz_boxed_2829_ = lean_unbox_usize(v_sz_2822_);
lean_dec(v_sz_2822_);
v_i_boxed_2830_ = lean_unbox_usize(v_i_2823_);
lean_dec(v_i_2823_);
v_res_2831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_2820_, v_post_2821_, v_sz_boxed_2829_, v_i_boxed_2830_, v_bs_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_2832_, lean_object* v_post_2833_, lean_object* v_x_2834_, lean_object* v_x_2835_, lean_object* v_x_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_pre_2832_, v_post_2833_, v_x_2834_, v_x_2835_, v_x_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___boxed(lean_object* v_pre_2842_, lean_object* v_post_2843_, lean_object* v_e_2844_, lean_object* v_a_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2842_, v_post_2843_, v_e_2844_, v_a_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v_a_2845_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_object* v_00_u03b1_2850_, lean_object* v_x_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = lean_apply_1(v_x_2851_, lean_box(0));
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2857_, lean_object* v_x_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(v_00_u03b1_2857_, v_x_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
return v_res_2862_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = lean_obj_once(&l_Lean_Expr_checkMaxShared___closed__1, &l_Lean_Expr_checkMaxShared___closed__1_once, _init_l_Lean_Expr_checkMaxShared___closed__1);
v___x_2864_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2864_, 0, lean_box(0));
lean_closure_set(v___x_2864_, 1, lean_box(0));
lean_closure_set(v___x_2864_, 2, v___x_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(lean_object* v_input_2865_, lean_object* v_pre_2866_, lean_object* v_post_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v_a_2873_; lean_object* v___x_2874_; 
v___x_2871_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___closed__0);
v___x_2872_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_2871_, v___y_2868_, v___y_2869_);
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref(v___x_2872_);
v___x_2874_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_2866_, v_post_2867_, v_input_2865_, v_a_2873_, v___y_2868_, v___y_2869_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v___x_2876_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2876_, 0, lean_box(0));
lean_closure_set(v___x_2876_, 1, lean_box(0));
lean_closure_set(v___x_2876_, 2, v_a_2873_);
v___x_2877_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_2876_, v___y_2868_, v___y_2869_);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v___x_2877_, 0);
lean_dec(v_unused_2885_);
v___x_2879_ = v___x_2877_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_dec(v___x_2877_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v_a_2875_);
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2875_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
else
{
lean_dec(v_a_2873_);
return v___x_2874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___boxed(lean_object* v_input_2886_, lean_object* v_pre_2887_, lean_object* v_post_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_input_2886_, v_pre_2887_, v_post_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object* v_e_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
uint8_t v___x_2899_; 
v___x_2899_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_2895_);
if (v___x_2899_ == 0)
{
lean_object* v_pre_2900_; lean_object* v___f_2901_; lean_object* v___x_2902_; 
v_pre_2900_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__0));
v___f_2901_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__1));
v___x_2902_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_e_2895_, v_pre_2900_, v___f_2901_, v_a_2896_, v_a_2897_);
return v___x_2902_;
}
else
{
lean_object* v___x_2903_; 
v___x_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2903_, 0, v_e_2895_);
return v___x_2903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___boxed(lean_object* v_e_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_Meta_Sym_normalizeLevels(v_e_2904_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_2909_, lean_object* v_m_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___redArg(v_m_2910_, v_a_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2913_, lean_object* v_m_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_00_u03b2_2913_, v_m_2914_, v_a_2915_);
lean_dec_ref(v_a_2915_);
lean_dec_ref(v_m_2914_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_2917_, lean_object* v_ref_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_2918_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2923_, lean_object* v_ref_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_2923_, v_ref_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___redArg();
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6_spec__9(v_00_u03b1_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6(lean_object* v_00_u03b1_2939_, lean_object* v_x_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___redArg(v_x_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b1_2946_, lean_object* v_x_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__6(v_00_u03b1_2946_, v_x_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_2953_, lean_object* v_m_2954_, lean_object* v_a_2955_, lean_object* v_b_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7___redArg(v_m_2954_, v_a_2955_, v_b_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_2958_, lean_object* v_a_2959_, lean_object* v_x_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___redArg(v_a_2959_, v_x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2962_, lean_object* v_a_2963_, lean_object* v_x_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4_spec__5(v_00_u03b2_2962_, v_a_2963_, v_x_2964_);
lean_dec(v_x_2964_);
lean_dec_ref(v_a_2963_);
return v_res_2965_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_2966_, lean_object* v_a_2967_, lean_object* v_x_2968_){
_start:
{
uint8_t v___x_2969_; 
v___x_2969_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___redArg(v_a_2967_, v_x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_2970_, lean_object* v_a_2971_, lean_object* v_x_2972_){
_start:
{
uint8_t v_res_2973_; lean_object* v_r_2974_; 
v_res_2973_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_2970_, v_a_2971_, v_x_2972_);
lean_dec(v_x_2972_);
lean_dec_ref(v_a_2971_);
v_r_2974_ = lean_box(v_res_2973_);
return v_r_2974_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_2975_, lean_object* v_data_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12___redArg(v_data_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13(lean_object* v_00_u03b2_2978_, lean_object* v_a_2979_, lean_object* v_b_2980_, lean_object* v_x_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__13___redArg(v_a_2979_, v_b_2980_, v_x_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13(lean_object* v_00_u03b2_2983_, lean_object* v_i_2984_, lean_object* v_source_2985_, lean_object* v_target_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v_i_2984_, v_source_2985_, v_target_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14(lean_object* v_00_u03b2_2988_, lean_object* v_x_2989_, lean_object* v_x_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_x_2989_, v_x_2990_);
return v___x_2991_;
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
