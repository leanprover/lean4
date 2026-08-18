// Lean compiler output
// Module: Lean.Meta.Sym.Apply
// Imports: public import Lean.Meta.Sym.Pattern import Lean.Util.CollectFVars import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_unify_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkPatternFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_mkPatternFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_sym_pre"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 124, 57, 118, 127, 154, 73, 9)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2;
static const lean_array_object l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4;
static const lean_ctor_object l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3_value),((lean_object*)&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3_value)}};
static const lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "rule is not applicable to goal"};
static const lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1;
static const lean_string_object l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rule:"};
static const lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(size_t v_sz_1_, size_t v_i_2_, lean_object* v_bs_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_usize_dec_lt(v_i_2_, v_sz_1_);
if (v___x_4_ == 0)
{
return v_bs_3_;
}
else
{
lean_object* v_v_5_; uint8_t v_isInstance_6_; lean_object* v___x_7_; lean_object* v_bs_x27_8_; size_t v___x_9_; size_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_v_5_ = lean_array_uget_borrowed(v_bs_3_, v_i_2_);
v_isInstance_6_ = lean_ctor_get_uint8(v_v_5_, 1);
v___x_7_ = lean_unsigned_to_nat(0u);
v_bs_x27_8_ = lean_array_uset(v_bs_3_, v_i_2_, v___x_7_);
v___x_9_ = ((size_t)1ULL);
v___x_10_ = lean_usize_add(v_i_2_, v___x_9_);
v___x_11_ = lean_box(v_isInstance_6_);
v___x_12_ = lean_array_uset(v_bs_x27_8_, v_i_2_, v___x_11_);
v_i_2_ = v___x_10_;
v_bs_3_ = v___x_12_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5___boxed(lean_object* v_sz_14_, lean_object* v_i_15_, lean_object* v_bs_16_){
_start:
{
size_t v_sz_boxed_17_; size_t v_i_boxed_18_; lean_object* v_res_19_; 
v_sz_boxed_17_ = lean_unbox_usize(v_sz_14_);
lean_dec(v_sz_14_);
v_i_boxed_18_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(v_sz_boxed_17_, v_i_boxed_18_, v_bs_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(lean_object* v_as_23_, size_t v_sz_24_, size_t v_i_25_, lean_object* v_b_26_){
_start:
{
lean_object* v_a_28_; uint8_t v___x_32_; 
v___x_32_ = lean_usize_dec_lt(v_i_25_, v_sz_24_);
if (v___x_32_ == 0)
{
return v_b_26_;
}
else
{
lean_object* v_a_33_; 
v_a_33_ = lean_array_uget_borrowed(v_as_23_, v_i_25_);
if (lean_obj_tag(v_a_33_) == 2)
{
lean_object* v_pre_34_; lean_object* v_i_35_; lean_object* v_auxPrefix_36_; uint8_t v___x_37_; 
v_pre_34_ = lean_ctor_get(v_a_33_, 0);
v_i_35_ = lean_ctor_get(v_a_33_, 1);
v_auxPrefix_36_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1));
v___x_37_ = lean_name_eq(v_pre_34_, v_auxPrefix_36_);
if (v___x_37_ == 0)
{
v_a_28_ = v_b_26_;
goto v___jp_27_;
}
else
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_box(v___x_37_);
v___x_39_ = lean_array_set(v_b_26_, v_i_35_, v___x_38_);
v_a_28_ = v___x_39_;
goto v___jp_27_;
}
}
else
{
v_a_28_ = v_b_26_;
goto v___jp_27_;
}
}
v___jp_27_:
{
size_t v___x_29_; size_t v___x_30_; 
v___x_29_ = ((size_t)1ULL);
v___x_30_ = lean_usize_add(v_i_25_, v___x_29_);
v_i_25_ = v___x_30_;
v_b_26_ = v_a_28_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___boxed(lean_object* v_as_40_, lean_object* v_sz_41_, lean_object* v_i_42_, lean_object* v_b_43_){
_start:
{
size_t v_sz_boxed_44_; size_t v_i_boxed_45_; lean_object* v_res_46_; 
v_sz_boxed_44_ = lean_unbox_usize(v_sz_41_);
lean_dec(v_sz_41_);
v_i_boxed_45_ = lean_unbox_usize(v_i_42_);
lean_dec(v_i_42_);
v_res_46_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(v_as_40_, v_sz_boxed_44_, v_i_boxed_45_, v_b_43_);
lean_dec_ref(v_as_40_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(lean_object* v_auxVars_47_, size_t v_sz_48_, size_t v_i_49_, lean_object* v_bs_50_){
_start:
{
uint8_t v___x_51_; 
v___x_51_ = lean_usize_dec_lt(v_i_49_, v_sz_48_);
if (v___x_51_ == 0)
{
return v_bs_50_;
}
else
{
lean_object* v_v_52_; lean_object* v___x_53_; lean_object* v_bs_x27_54_; lean_object* v___x_55_; lean_object* v___x_56_; size_t v___x_57_; size_t v___x_58_; lean_object* v___x_59_; 
v_v_52_ = lean_array_uget(v_bs_50_, v_i_49_);
v___x_53_ = lean_unsigned_to_nat(0u);
v_bs_x27_54_ = lean_array_uset(v_bs_50_, v_i_49_, v___x_53_);
v___x_55_ = lean_usize_to_nat(v_i_49_);
v___x_56_ = lean_expr_instantiate_rev_range(v_v_52_, v___x_53_, v___x_55_, v_auxVars_47_);
lean_dec(v___x_55_);
lean_dec(v_v_52_);
v___x_57_ = ((size_t)1ULL);
v___x_58_ = lean_usize_add(v_i_49_, v___x_57_);
v___x_59_ = lean_array_uset(v_bs_x27_54_, v_i_49_, v___x_56_);
v_i_49_ = v___x_58_;
v_bs_50_ = v___x_59_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg___boxed(lean_object* v_auxVars_61_, lean_object* v_sz_62_, lean_object* v_i_63_, lean_object* v_bs_64_){
_start:
{
size_t v_sz_boxed_65_; size_t v_i_boxed_66_; lean_object* v_res_67_; 
v_sz_boxed_65_ = lean_unbox_usize(v_sz_62_);
lean_dec(v_sz_62_);
v_i_boxed_66_ = lean_unbox_usize(v_i_63_);
lean_dec(v_i_63_);
v_res_67_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_61_, v_sz_boxed_65_, v_i_boxed_66_, v_bs_64_);
lean_dec_ref(v_auxVars_61_);
return v_res_67_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(lean_object* v_upperBound_68_, lean_object* v___x_69_, lean_object* v___x_70_, lean_object* v___x_71_, lean_object* v_a_72_, uint8_t v_b_73_){
_start:
{
uint8_t v_a_75_; uint8_t v___x_79_; 
v___x_79_ = lean_nat_dec_lt(v_a_72_, v_upperBound_68_);
if (v___x_79_ == 0)
{
lean_dec(v_a_72_);
return v_b_73_;
}
else
{
uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_80_ = 0;
v___x_81_ = lean_box(v___x_80_);
v___x_82_ = lean_array_get(v___x_81_, v___x_69_, v_a_72_);
lean_dec(v___x_81_);
v___x_83_ = lean_unbox(v___x_82_);
lean_dec(v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_84_ = l_Lean_instInhabitedExpr;
v___x_85_ = lean_array_get_borrowed(v___x_84_, v___x_70_, v_a_72_);
v___x_86_ = l_Lean_Expr_fvarId_x21(v___x_71_);
v___x_87_ = l_Lean_Expr_containsFVar(v___x_85_, v___x_86_);
lean_dec(v___x_86_);
if (v___x_87_ == 0)
{
v_a_75_ = v_b_73_;
goto v___jp_74_;
}
else
{
lean_dec(v_a_72_);
return v___x_87_;
}
}
else
{
v_a_75_ = v_b_73_;
goto v___jp_74_;
}
}
v___jp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_unsigned_to_nat(1u);
v___x_77_ = lean_nat_add(v_a_72_, v___x_76_);
lean_dec(v_a_72_);
v_a_72_ = v___x_77_;
v_b_73_ = v_a_75_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg___boxed(lean_object* v_upperBound_88_, lean_object* v___x_89_, lean_object* v___x_90_, lean_object* v___x_91_, lean_object* v_a_92_, lean_object* v_b_93_){
_start:
{
uint8_t v_b_boxed_94_; uint8_t v_res_95_; lean_object* v_r_96_; 
v_b_boxed_94_ = lean_unbox(v_b_93_);
v_res_95_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_upperBound_88_, v___x_89_, v___x_90_, v___x_91_, v_a_92_, v_b_boxed_94_);
lean_dec_ref(v___x_91_);
lean_dec_ref(v___x_90_);
lean_dec_ref(v___x_89_);
lean_dec(v_upperBound_88_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(lean_object* v_upperBound_97_, lean_object* v___x_98_, lean_object* v_numArgs_99_, lean_object* v_auxVars_100_, lean_object* v___x_101_, lean_object* v_a_102_, lean_object* v_b_103_){
_start:
{
lean_object* v_a_105_; uint8_t v___x_109_; 
v___x_109_ = lean_nat_dec_lt(v_a_102_, v_upperBound_97_);
if (v___x_109_ == 0)
{
lean_dec(v_a_102_);
return v_b_103_;
}
else
{
lean_object* v_fst_110_; lean_object* v_snd_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_136_; 
v_fst_110_ = lean_ctor_get(v_b_103_, 0);
v_snd_111_ = lean_ctor_get(v_b_103_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_b_103_);
if (v_isSharedCheck_136_ == 0)
{
v___x_113_ = v_b_103_;
v_isShared_114_ = v_isSharedCheck_136_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_snd_111_);
lean_inc(v_fst_110_);
lean_dec(v_b_103_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_136_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_115_ = 0;
v___x_116_ = lean_box(v___x_115_);
v___x_117_ = lean_array_get(v___x_116_, v___x_98_, v_a_102_);
lean_dec(v___x_116_);
v___x_118_ = lean_unbox(v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; uint8_t v___x_124_; 
v___x_119_ = l_Lean_instInhabitedExpr;
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_add(v_a_102_, v___x_120_);
v___x_122_ = lean_array_get_borrowed(v___x_119_, v_auxVars_100_, v_a_102_);
v___x_123_ = lean_unbox(v___x_117_);
lean_dec(v___x_117_);
v___x_124_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_numArgs_99_, v___x_98_, v___x_101_, v___x_122_, v___x_121_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_a_102_);
v___x_125_ = lean_array_push(v_snd_111_, v_a_102_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_125_);
v___x_127_ = v___x_113_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_fst_110_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
v_a_105_ = v___x_127_;
goto v___jp_104_;
}
}
else
{
lean_object* v___x_129_; lean_object* v___x_131_; 
lean_inc(v_a_102_);
v___x_129_ = lean_array_push(v_fst_110_, v_a_102_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_129_);
v___x_131_ = v___x_113_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_snd_111_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
v_a_105_ = v___x_131_;
goto v___jp_104_;
}
}
}
else
{
lean_object* v___x_134_; 
lean_dec(v___x_117_);
if (v_isShared_114_ == 0)
{
v___x_134_ = v___x_113_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_fst_110_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_snd_111_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
v_a_105_ = v___x_134_;
goto v___jp_104_;
}
}
}
}
v___jp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_add(v_a_102_, v___x_106_);
lean_dec(v_a_102_);
v_a_102_ = v___x_107_;
v_b_103_ = v_a_105_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg___boxed(lean_object* v_upperBound_137_, lean_object* v___x_138_, lean_object* v_numArgs_139_, lean_object* v_auxVars_140_, lean_object* v___x_141_, lean_object* v_a_142_, lean_object* v_b_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_upperBound_137_, v___x_138_, v_numArgs_139_, v_auxVars_140_, v___x_141_, v_a_142_, v_b_143_);
lean_dec_ref(v___x_141_);
lean_dec_ref(v_auxVars_140_);
lean_dec(v_numArgs_139_);
lean_dec_ref(v___x_138_);
lean_dec(v_upperBound_137_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(size_t v_sz_145_, size_t v_i_146_, lean_object* v_bs_147_){
_start:
{
uint8_t v___x_148_; 
v___x_148_ = lean_usize_dec_lt(v_i_146_, v_sz_145_);
if (v___x_148_ == 0)
{
return v_bs_147_;
}
else
{
lean_object* v_auxPrefix_149_; lean_object* v___x_150_; lean_object* v_bs_x27_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; size_t v___x_155_; size_t v___x_156_; lean_object* v___x_157_; 
v_auxPrefix_149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1));
v___x_150_ = lean_unsigned_to_nat(0u);
v_bs_x27_151_ = lean_array_uset(v_bs_147_, v_i_146_, v___x_150_);
v___x_152_ = lean_usize_to_nat(v_i_146_);
v___x_153_ = l_Lean_Name_num___override(v_auxPrefix_149_, v___x_152_);
v___x_154_ = l_Lean_mkFVar(v___x_153_);
v___x_155_ = ((size_t)1ULL);
v___x_156_ = lean_usize_add(v_i_146_, v___x_155_);
v___x_157_ = lean_array_uset(v_bs_x27_151_, v_i_146_, v___x_154_);
v_i_146_ = v___x_156_;
v_bs_147_ = v___x_157_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg___boxed(lean_object* v_sz_159_, lean_object* v_i_160_, lean_object* v_bs_161_){
_start:
{
size_t v_sz_boxed_162_; size_t v_i_boxed_163_; lean_object* v_res_164_; 
v_sz_boxed_162_ = lean_unbox_usize(v_sz_159_);
lean_dec(v_sz_159_);
v_i_boxed_163_ = lean_unbox_usize(v_i_160_);
lean_dec(v_i_160_);
v_res_164_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_sz_boxed_162_, v_i_boxed_163_, v_bs_161_);
return v_res_164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0(void){
_start:
{
lean_object* v_cellCount_165_; lean_object* v___x_166_; 
v_cellCount_165_ = lean_unsigned_to_nat(16u);
v___x_166_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_165_);
return v___x_166_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1(void){
_start:
{
lean_object* v_cellCount_167_; lean_object* v___x_168_; 
v_cellCount_167_ = lean_unsigned_to_nat(16u);
v___x_168_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_167_);
return v___x_168_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_169_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1);
v___x_170_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
lean_ctor_set(v___x_172_, 2, v___x_169_);
return v___x_172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = ((lean_object*)(l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3));
v___x_176_ = lean_box(1);
v___x_177_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2);
v___x_178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
lean_ctor_set(v___x_178_, 2, v___x_175_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(lean_object* v_pattern_181_){
_start:
{
lean_object* v_varTypes_182_; lean_object* v_varInfos_x3f_183_; lean_object* v_pattern_184_; lean_object* v_numArgs_185_; lean_object* v___y_187_; 
v_varTypes_182_ = lean_ctor_get(v_pattern_181_, 1);
lean_inc_ref(v_varTypes_182_);
v_varInfos_x3f_183_ = lean_ctor_get(v_pattern_181_, 2);
lean_inc(v_varInfos_x3f_183_);
v_pattern_184_ = lean_ctor_get(v_pattern_181_, 3);
lean_inc_ref(v_pattern_184_);
lean_dec_ref(v_pattern_181_);
v_numArgs_185_ = lean_array_get_size(v_varTypes_182_);
if (lean_obj_tag(v_varInfos_x3f_183_) == 1)
{
lean_object* v_val_205_; size_t v_sz_206_; size_t v___x_207_; lean_object* v___x_208_; 
v_val_205_ = lean_ctor_get(v_varInfos_x3f_183_, 0);
lean_inc(v_val_205_);
lean_dec_ref_known(v_varInfos_x3f_183_, 1);
v_sz_206_ = lean_array_size(v_val_205_);
v___x_207_ = ((size_t)0ULL);
v___x_208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(v_sz_206_, v___x_207_, v_val_205_);
v___y_187_ = v___x_208_;
goto v___jp_186_;
}
else
{
uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec(v_varInfos_x3f_183_);
v___x_209_ = 0;
v___x_210_ = lean_box(v___x_209_);
v___x_211_ = lean_mk_array(v_numArgs_185_, v___x_210_);
v___y_187_ = v___x_211_;
goto v___jp_186_;
}
v___jp_186_:
{
size_t v_sz_188_; size_t v___x_189_; lean_object* v_auxVars_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v_fvarIds_195_; size_t v_sz_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v_fst_201_; lean_object* v_snd_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_sz_188_ = lean_array_size(v_varTypes_182_);
v___x_189_ = ((size_t)0ULL);
lean_inc_ref(v_varTypes_182_);
v_auxVars_190_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_sz_188_, v___x_189_, v_varTypes_182_);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4);
v___x_193_ = lean_expr_instantiate_rev(v_pattern_184_, v_auxVars_190_);
lean_dec_ref(v_pattern_184_);
v___x_194_ = l_Lean_collectFVars(v___x_192_, v___x_193_);
v_fvarIds_195_ = lean_ctor_get(v___x_194_, 2);
lean_inc_ref(v_fvarIds_195_);
lean_dec_ref(v___x_194_);
v_sz_196_ = lean_array_size(v_fvarIds_195_);
v___x_197_ = ((lean_object*)(l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__5));
v___x_198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(v_fvarIds_195_, v_sz_196_, v___x_189_, v___y_187_);
lean_dec_ref(v_fvarIds_195_);
v___x_199_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_190_, v_sz_188_, v___x_189_, v_varTypes_182_);
v___x_200_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_numArgs_185_, v___x_198_, v_numArgs_185_, v_auxVars_190_, v___x_199_, v___x_191_, v___x_197_);
lean_dec_ref(v___x_199_);
lean_dec_ref(v_auxVars_190_);
lean_dec_ref(v___x_198_);
v_fst_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_fst_201_);
v_snd_202_ = lean_ctor_get(v___x_200_, 1);
lean_inc(v_snd_202_);
lean_dec_ref(v___x_200_);
v___x_203_ = l_Array_append___redArg(v_snd_202_, v_fst_201_);
lean_dec(v_fst_201_);
v___x_204_ = lean_array_to_list(v___x_203_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(lean_object* v_as_212_, size_t v_sz_213_, size_t v_i_214_, lean_object* v_bs_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_sz_213_, v_i_214_, v_bs_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___boxed(lean_object* v_as_217_, lean_object* v_sz_218_, lean_object* v_i_219_, lean_object* v_bs_220_){
_start:
{
size_t v_sz_boxed_221_; size_t v_i_boxed_222_; lean_object* v_res_223_; 
v_sz_boxed_221_ = lean_unbox_usize(v_sz_218_);
lean_dec(v_sz_218_);
v_i_boxed_222_ = lean_unbox_usize(v_i_219_);
lean_dec(v_i_219_);
v_res_223_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(v_as_217_, v_sz_boxed_221_, v_i_boxed_222_, v_bs_220_);
lean_dec_ref(v_as_217_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(lean_object* v_auxVars_224_, lean_object* v_as_225_, size_t v_sz_226_, size_t v_i_227_, lean_object* v_bs_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_224_, v_sz_226_, v_i_227_, v_bs_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___boxed(lean_object* v_auxVars_230_, lean_object* v_as_231_, lean_object* v_sz_232_, lean_object* v_i_233_, lean_object* v_bs_234_){
_start:
{
size_t v_sz_boxed_235_; size_t v_i_boxed_236_; lean_object* v_res_237_; 
v_sz_boxed_235_ = lean_unbox_usize(v_sz_232_);
lean_dec(v_sz_232_);
v_i_boxed_236_ = lean_unbox_usize(v_i_233_);
lean_dec(v_i_233_);
v_res_237_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(v_auxVars_230_, v_as_231_, v_sz_boxed_235_, v_i_boxed_236_, v_bs_234_);
lean_dec_ref(v_as_231_);
lean_dec_ref(v_auxVars_230_);
return v_res_237_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(lean_object* v_upperBound_238_, lean_object* v___x_239_, lean_object* v___x_240_, lean_object* v___x_241_, lean_object* v_inst_242_, lean_object* v_R_243_, lean_object* v_a_244_, uint8_t v_b_245_, lean_object* v_c_246_){
_start:
{
uint8_t v___x_247_; 
v___x_247_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_upperBound_238_, v___x_239_, v___x_240_, v___x_241_, v_a_244_, v_b_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___boxed(lean_object* v_upperBound_248_, lean_object* v___x_249_, lean_object* v___x_250_, lean_object* v___x_251_, lean_object* v_inst_252_, lean_object* v_R_253_, lean_object* v_a_254_, lean_object* v_b_255_, lean_object* v_c_256_){
_start:
{
uint8_t v_b_boxed_257_; uint8_t v_res_258_; lean_object* v_r_259_; 
v_b_boxed_257_ = lean_unbox(v_b_255_);
v_res_258_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(v_upperBound_248_, v___x_249_, v___x_250_, v___x_251_, v_inst_252_, v_R_253_, v_a_254_, v_b_boxed_257_, v_c_256_);
lean_dec_ref(v___x_251_);
lean_dec_ref(v___x_250_);
lean_dec_ref(v___x_249_);
lean_dec(v_upperBound_248_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(lean_object* v_upperBound_260_, lean_object* v___x_261_, lean_object* v_numArgs_262_, lean_object* v_auxVars_263_, lean_object* v___x_264_, lean_object* v_inst_265_, lean_object* v_R_266_, lean_object* v_a_267_, lean_object* v_b_268_, lean_object* v_c_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_upperBound_260_, v___x_261_, v_numArgs_262_, v_auxVars_263_, v___x_264_, v_a_267_, v_b_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___boxed(lean_object* v_upperBound_271_, lean_object* v___x_272_, lean_object* v_numArgs_273_, lean_object* v_auxVars_274_, lean_object* v___x_275_, lean_object* v_inst_276_, lean_object* v_R_277_, lean_object* v_a_278_, lean_object* v_b_279_, lean_object* v_c_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(v_upperBound_271_, v___x_272_, v_numArgs_273_, v_auxVars_274_, v___x_275_, v_inst_276_, v_R_277_, v_a_278_, v_b_279_, v_c_280_);
lean_dec_ref(v___x_275_);
lean_dec_ref(v_auxVars_274_);
lean_dec(v_numArgs_273_);
lean_dec_ref(v___x_272_);
lean_dec(v_upperBound_271_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object* v_declName_282_, lean_object* v_num_x3f_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_289_; 
lean_inc(v_declName_282_);
v___x_289_ = l_Lean_Meta_Sym_mkPatternFromDecl(v_declName_282_, v_num_x3f_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_301_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_301_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_301_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_301_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
lean_inc(v_a_290_);
v___x_294_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(v_a_290_);
v___x_295_ = lean_box(0);
v___x_296_ = l_Lean_mkConst(v_declName_282_, v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_a_290_);
lean_ctor_set(v___x_297_, 2, v___x_294_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_297_);
v___x_299_ = v___x_292_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec(v_declName_282_);
v_a_302_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_289_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_289_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl___boxed(lean_object* v_declName_310_, lean_object* v_num_x3f_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v_declName_310_, v_num_x3f_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_num_x3f_311_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
if (lean_obj_tag(v_a_318_) == 0)
{
lean_object* v___x_320_; 
v___x_320_ = l_List_reverse___redArg(v_a_319_);
return v___x_320_;
}
else
{
lean_object* v_head_321_; lean_object* v_tail_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_331_; 
v_head_321_ = lean_ctor_get(v_a_318_, 0);
v_tail_322_ = lean_ctor_get(v_a_318_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_a_318_);
if (v_isSharedCheck_331_ == 0)
{
v___x_324_ = v_a_318_;
v_isShared_325_ = v_isSharedCheck_331_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_tail_322_);
lean_inc(v_head_321_);
lean_dec(v_a_318_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_331_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = l_Lean_mkLevelParam(v_head_321_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v_a_319_);
lean_ctor_set(v___x_324_, 0, v___x_326_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_a_319_);
v___x_328_ = v_reuseFailAlloc_330_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
v_a_318_ = v_tail_322_;
v_a_319_ = v___x_328_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object* v_e_332_, lean_object* v_levelParams_333_, lean_object* v_num_x3f_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_340_; 
lean_inc(v_levelParams_333_);
lean_inc_ref(v_e_332_);
v___x_340_ = l_Lean_Meta_Sym_mkPatternFromExpr(v_e_332_, v_levelParams_333_, v_num_x3f_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_354_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_354_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_354_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_354_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v_levelParams_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
v_levelParams_345_ = lean_ctor_get(v_a_341_, 0);
lean_inc(v_a_341_);
v___x_346_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(v_a_341_);
v___x_347_ = lean_box(0);
lean_inc(v_levelParams_345_);
v___x_348_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(v_levelParams_345_, v___x_347_);
v___x_349_ = l_Lean_Expr_instantiateLevelParams(v_e_332_, v_levelParams_333_, v___x_348_);
lean_dec_ref(v_e_332_);
v___x_350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v_a_341_);
lean_ctor_set(v___x_350_, 2, v___x_346_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_350_);
v___x_352_ = v___x_343_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec(v_levelParams_333_);
lean_dec_ref(v_e_332_);
v_a_355_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_340_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_340_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr___boxed(lean_object* v_e_363_, lean_object* v_levelParams_364_, lean_object* v_num_x3f_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_e_363_, v_levelParams_364_, v_num_x3f_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_num_x3f_365_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(lean_object* v_expr_372_, lean_object* v_pattern_373_, lean_object* v_result_374_){
_start:
{
if (lean_obj_tag(v_expr_372_) == 4)
{
lean_object* v_us_381_; 
v_us_381_ = lean_ctor_get(v_expr_372_, 1);
if (lean_obj_tag(v_us_381_) == 0)
{
lean_object* v_declName_382_; lean_object* v_us_383_; lean_object* v_args_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec_ref(v_pattern_373_);
v_declName_382_ = lean_ctor_get(v_expr_372_, 0);
lean_inc(v_declName_382_);
lean_dec_ref_known(v_expr_372_, 2);
v_us_383_ = lean_ctor_get(v_result_374_, 0);
lean_inc(v_us_383_);
v_args_384_ = lean_ctor_get(v_result_374_, 1);
lean_inc_ref(v_args_384_);
lean_dec_ref(v_result_374_);
v___x_385_ = l_Lean_mkConst(v_declName_382_, v_us_383_);
v___x_386_ = l_Lean_mkAppN(v___x_385_, v_args_384_);
lean_dec_ref(v_args_384_);
return v___x_386_;
}
else
{
goto v___jp_375_;
}
}
else
{
goto v___jp_375_;
}
v___jp_375_:
{
lean_object* v_levelParams_376_; lean_object* v_us_377_; lean_object* v_args_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_levelParams_376_ = lean_ctor_get(v_pattern_373_, 0);
lean_inc(v_levelParams_376_);
lean_dec_ref(v_pattern_373_);
v_us_377_ = lean_ctor_get(v_result_374_, 0);
lean_inc(v_us_377_);
v_args_378_ = lean_ctor_get(v_result_374_, 1);
lean_inc_ref(v_args_378_);
lean_dec_ref(v_result_374_);
v___x_379_ = l_Lean_Expr_instantiateLevelParams(v_expr_372_, v_levelParams_376_, v_us_377_);
lean_dec_ref(v_expr_372_);
v___x_380_ = l_Lean_mkAppN(v___x_379_, v_args_378_);
lean_dec_ref(v_args_378_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx(lean_object* v_x_387_){
_start:
{
if (lean_obj_tag(v_x_387_) == 0)
{
lean_object* v___x_388_; 
v___x_388_ = lean_unsigned_to_nat(0u);
return v___x_388_;
}
else
{
lean_object* v___x_389_; 
v___x_389_ = lean_unsigned_to_nat(1u);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___boxed(lean_object* v_x_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Meta_Sym_ApplyResult_ctorIdx(v_x_390_);
lean_dec(v_x_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(lean_object* v_t_392_, lean_object* v_k_393_){
_start:
{
if (lean_obj_tag(v_t_392_) == 0)
{
return v_k_393_;
}
else
{
lean_object* v_mvarIds_394_; lean_object* v___x_395_; 
v_mvarIds_394_ = lean_ctor_get(v_t_392_, 0);
lean_inc(v_mvarIds_394_);
lean_dec_ref_known(v_t_392_, 1);
v___x_395_ = lean_apply_1(v_k_393_, v_mvarIds_394_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim(lean_object* v_motive_396_, lean_object* v_ctorIdx_397_, lean_object* v_t_398_, lean_object* v_h_399_, lean_object* v_k_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_398_, v_k_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___boxed(lean_object* v_motive_402_, lean_object* v_ctorIdx_403_, lean_object* v_t_404_, lean_object* v_h_405_, lean_object* v_k_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Meta_Sym_ApplyResult_ctorElim(v_motive_402_, v_ctorIdx_403_, v_t_404_, v_h_405_, v_k_406_);
lean_dec(v_ctorIdx_403_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim___redArg(lean_object* v_t_408_, lean_object* v_failed_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_408_, v_failed_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim(lean_object* v_motive_411_, lean_object* v_t_412_, lean_object* v_h_413_, lean_object* v_failed_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_412_, v_failed_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim___redArg(lean_object* v_t_416_, lean_object* v_goals_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_416_, v_goals_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim(lean_object* v_motive_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_goals_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_420_, v_goals_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(lean_object* v_x_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; 
lean_inc(v___y_426_);
lean_inc_ref(v___y_425_);
v___x_432_ = lean_apply_7(v_x_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, lean_box(0));
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed(lean_object* v_x_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(v_x_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(lean_object* v_mvarId_442_, lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___f_451_; lean_object* v___x_452_; 
lean_inc(v___y_445_);
lean_inc_ref(v___y_444_);
v___f_451_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_451_, 0, v_x_443_);
lean_closure_set(v___f_451_, 1, v___y_444_);
lean_closure_set(v___f_451_, 2, v___y_445_);
v___x_452_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_442_, v___f_451_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_452_) == 0)
{
return v___x_452_;
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___boxed(lean_object* v_mvarId_461_, lean_object* v_x_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_461_, v_x_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(lean_object* v_00_u03b1_471_, lean_object* v_mvarId_472_, lean_object* v_x_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_472_, v_x_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___boxed(lean_object* v_00_u03b1_482_, lean_object* v_mvarId_483_, lean_object* v_x_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(v_00_u03b1_482_, v_mvarId_483_, v_x_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(lean_object* v_val_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
if (lean_obj_tag(v_a_494_) == 0)
{
lean_object* v___x_496_; 
v___x_496_ = l_List_reverse___redArg(v_a_495_);
return v___x_496_;
}
else
{
lean_object* v_head_497_; lean_object* v_tail_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_510_; 
v_head_497_ = lean_ctor_get(v_a_494_, 0);
v_tail_498_ = lean_ctor_get(v_a_494_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v_a_494_);
if (v_isSharedCheck_510_ == 0)
{
v___x_500_ = v_a_494_;
v_isShared_501_ = v_isSharedCheck_510_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_tail_498_);
lean_inc(v_head_497_);
lean_dec(v_a_494_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_510_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v_args_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v_args_502_ = lean_ctor_get(v_val_493_, 1);
v___x_503_ = l_Lean_instInhabitedExpr;
v___x_504_ = lean_array_get_borrowed(v___x_503_, v_args_502_, v_head_497_);
lean_dec(v_head_497_);
v___x_505_ = l_Lean_Expr_mvarId_x21(v___x_504_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v_a_495_);
lean_ctor_set(v___x_500_, 0, v___x_505_);
v___x_507_ = v___x_500_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_a_495_);
v___x_507_ = v_reuseFailAlloc_509_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
v_a_494_ = v_tail_498_;
v_a_495_ = v___x_507_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1___boxed(lean_object* v_val_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(v_val_511_, v_a_512_, v_a_513_);
lean_dec_ref(v_val_511_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
lean_object* v_ks_519_; lean_object* v_vs_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_544_; 
v_ks_519_ = lean_ctor_get(v_x_515_, 0);
v_vs_520_ = lean_ctor_get(v_x_515_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_544_ == 0)
{
v___x_522_ = v_x_515_;
v_isShared_523_ = v_isSharedCheck_544_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_vs_520_);
lean_inc(v_ks_519_);
lean_dec(v_x_515_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_544_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_array_get_size(v_ks_519_);
v___x_525_ = lean_nat_dec_lt(v_x_516_, v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
lean_dec(v_x_516_);
v___x_526_ = lean_array_push(v_ks_519_, v_x_517_);
v___x_527_ = lean_array_push(v_vs_520_, v_x_518_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v___x_527_);
lean_ctor_set(v___x_522_, 0, v___x_526_);
v___x_529_ = v___x_522_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
else
{
lean_object* v_k_x27_531_; uint8_t v___x_532_; 
v_k_x27_531_ = lean_array_fget_borrowed(v_ks_519_, v_x_516_);
v___x_532_ = l_Lean_instBEqMVarId_beq(v_x_517_, v_k_x27_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_534_; 
if (v_isShared_523_ == 0)
{
v___x_534_ = v___x_522_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_ks_519_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_vs_520_);
v___x_534_ = v_reuseFailAlloc_538_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_x_516_, v___x_535_);
lean_dec(v_x_516_);
v_x_515_ = v___x_534_;
v_x_516_ = v___x_536_;
goto _start;
}
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_539_ = lean_array_fset(v_ks_519_, v_x_516_, v_x_517_);
v___x_540_ = lean_array_fset(v_vs_520_, v_x_516_, v_x_518_);
lean_dec(v_x_516_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v___x_540_);
lean_ctor_set(v___x_522_, 0, v___x_539_);
v___x_542_ = v___x_522_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_545_, lean_object* v_k_546_, lean_object* v_v_547_){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_545_, v___x_548_, v_k_546_, v_v_547_);
return v___x_549_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(lean_object* v_x_551_, size_t v_x_552_, size_t v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
if (lean_obj_tag(v_x_551_) == 0)
{
lean_object* v_es_556_; size_t v___x_557_; size_t v___x_558_; lean_object* v_j_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_es_556_ = lean_ctor_get(v_x_551_, 0);
v___x_557_ = ((size_t)31ULL);
v___x_558_ = lean_usize_land(v_x_552_, v___x_557_);
v_j_559_ = lean_usize_to_nat(v___x_558_);
v___x_560_ = lean_array_get_size(v_es_556_);
v___x_561_ = lean_nat_dec_lt(v_j_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_dec(v_j_559_);
lean_dec(v_x_555_);
lean_dec(v_x_554_);
return v_x_551_;
}
else
{
lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_600_; 
lean_inc_ref(v_es_556_);
v_isSharedCheck_600_ = !lean_is_exclusive(v_x_551_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v_x_551_, 0);
lean_dec(v_unused_601_);
v___x_563_ = v_x_551_;
v_isShared_564_ = v_isSharedCheck_600_;
goto v_resetjp_562_;
}
else
{
lean_dec(v_x_551_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_600_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_v_565_; lean_object* v___x_566_; lean_object* v_xs_x27_567_; lean_object* v___y_569_; 
v_v_565_ = lean_array_fget(v_es_556_, v_j_559_);
v___x_566_ = lean_box(0);
v_xs_x27_567_ = lean_array_fset(v_es_556_, v_j_559_, v___x_566_);
switch(lean_obj_tag(v_v_565_))
{
case 0:
{
lean_object* v_key_574_; lean_object* v_val_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_585_; 
v_key_574_ = lean_ctor_get(v_v_565_, 0);
v_val_575_ = lean_ctor_get(v_v_565_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v_v_565_);
if (v_isSharedCheck_585_ == 0)
{
v___x_577_ = v_v_565_;
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_val_575_);
lean_inc(v_key_574_);
lean_dec(v_v_565_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
uint8_t v___x_579_; 
v___x_579_ = l_Lean_instBEqMVarId_beq(v_x_554_, v_key_574_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_del_object(v___x_577_);
v___x_580_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_574_, v_val_575_, v_x_554_, v_x_555_);
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
v___y_569_ = v___x_581_;
goto v___jp_568_;
}
else
{
lean_object* v___x_583_; 
lean_dec(v_val_575_);
lean_dec(v_key_574_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v_x_555_);
lean_ctor_set(v___x_577_, 0, v_x_554_);
v___x_583_ = v___x_577_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_x_554_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_x_555_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
v___y_569_ = v___x_583_;
goto v___jp_568_;
}
}
}
}
case 1:
{
lean_object* v_node_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_598_; 
v_node_586_ = lean_ctor_get(v_v_565_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_v_565_);
if (v_isSharedCheck_598_ == 0)
{
v___x_588_ = v_v_565_;
v_isShared_589_ = v_isSharedCheck_598_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_node_586_);
lean_dec(v_v_565_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_598_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
size_t v___x_590_; size_t v___x_591_; size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_590_ = ((size_t)5ULL);
v___x_591_ = lean_usize_shift_right(v_x_552_, v___x_590_);
v___x_592_ = ((size_t)1ULL);
v___x_593_ = lean_usize_add(v_x_553_, v___x_592_);
v___x_594_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_node_586_, v___x_591_, v___x_593_, v_x_554_, v_x_555_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_594_);
v___x_596_ = v___x_588_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
v___y_569_ = v___x_596_;
goto v___jp_568_;
}
}
}
default: 
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_x_554_);
lean_ctor_set(v___x_599_, 1, v_x_555_);
v___y_569_ = v___x_599_;
goto v___jp_568_;
}
}
v___jp_568_:
{
lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_570_ = lean_array_fset(v_xs_x27_567_, v_j_559_, v___y_569_);
lean_dec(v_j_559_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_570_);
v___x_572_ = v___x_563_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
else
{
lean_object* v_ks_602_; lean_object* v_vs_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_623_; 
v_ks_602_ = lean_ctor_get(v_x_551_, 0);
v_vs_603_ = lean_ctor_get(v_x_551_, 1);
v_isSharedCheck_623_ = !lean_is_exclusive(v_x_551_);
if (v_isSharedCheck_623_ == 0)
{
v___x_605_ = v_x_551_;
v_isShared_606_ = v_isSharedCheck_623_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_vs_603_);
lean_inc(v_ks_602_);
lean_dec(v_x_551_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_623_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_ks_602_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_vs_603_);
v___x_608_ = v_reuseFailAlloc_622_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v_newNode_609_; uint8_t v___y_611_; size_t v___x_617_; uint8_t v___x_618_; 
v_newNode_609_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v___x_608_, v_x_554_, v_x_555_);
v___x_617_ = ((size_t)7ULL);
v___x_618_ = lean_usize_dec_le(v___x_617_, v_x_553_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_619_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_609_);
v___x_620_ = lean_unsigned_to_nat(4u);
v___x_621_ = lean_nat_dec_lt(v___x_619_, v___x_620_);
lean_dec(v___x_619_);
v___y_611_ = v___x_621_;
goto v___jp_610_;
}
else
{
v___y_611_ = v___x_618_;
goto v___jp_610_;
}
v___jp_610_:
{
if (v___y_611_ == 0)
{
lean_object* v_ks_612_; lean_object* v_vs_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_ks_612_ = lean_ctor_get(v_newNode_609_, 0);
lean_inc_ref(v_ks_612_);
v_vs_613_ = lean_ctor_get(v_newNode_609_, 1);
lean_inc_ref(v_vs_613_);
lean_dec_ref(v_newNode_609_);
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_616_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_x_553_, v_ks_612_, v_vs_613_, v___x_614_, v___x_615_);
lean_dec_ref(v_vs_613_);
lean_dec_ref(v_ks_612_);
return v___x_616_;
}
else
{
return v_newNode_609_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_624_, lean_object* v_keys_625_, lean_object* v_vals_626_, lean_object* v_i_627_, lean_object* v_entries_628_){
_start:
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = lean_array_get_size(v_keys_625_);
v___x_630_ = lean_nat_dec_lt(v_i_627_, v___x_629_);
if (v___x_630_ == 0)
{
lean_dec(v_i_627_);
return v_entries_628_;
}
else
{
lean_object* v_k_631_; lean_object* v_v_632_; uint64_t v___x_633_; size_t v_h_634_; size_t v___x_635_; lean_object* v___x_636_; size_t v___x_637_; size_t v___x_638_; size_t v___x_639_; size_t v_h_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_k_631_ = lean_array_fget_borrowed(v_keys_625_, v_i_627_);
v_v_632_ = lean_array_fget_borrowed(v_vals_626_, v_i_627_);
v___x_633_ = l_Lean_instHashableMVarId_hash(v_k_631_);
v_h_634_ = lean_uint64_to_usize(v___x_633_);
v___x_635_ = ((size_t)5ULL);
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_sub(v_depth_624_, v___x_637_);
v___x_639_ = lean_usize_mul(v___x_635_, v___x_638_);
v_h_640_ = lean_usize_shift_right(v_h_634_, v___x_639_);
v___x_641_ = lean_nat_add(v_i_627_, v___x_636_);
lean_dec(v_i_627_);
lean_inc(v_v_632_);
lean_inc(v_k_631_);
v___x_642_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_entries_628_, v_h_640_, v_depth_624_, v_k_631_, v_v_632_);
v_i_627_ = v___x_641_;
v_entries_628_ = v___x_642_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_644_, lean_object* v_keys_645_, lean_object* v_vals_646_, lean_object* v_i_647_, lean_object* v_entries_648_){
_start:
{
size_t v_depth_boxed_649_; lean_object* v_res_650_; 
v_depth_boxed_649_ = lean_unbox_usize(v_depth_644_);
lean_dec(v_depth_644_);
v_res_650_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_649_, v_keys_645_, v_vals_646_, v_i_647_, v_entries_648_);
lean_dec_ref(v_vals_646_);
lean_dec_ref(v_keys_645_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
size_t v_x_3208__boxed_656_; size_t v_x_3209__boxed_657_; lean_object* v_res_658_; 
v_x_3208__boxed_656_ = lean_unbox_usize(v_x_652_);
lean_dec(v_x_652_);
v_x_3209__boxed_657_ = lean_unbox_usize(v_x_653_);
lean_dec(v_x_653_);
v_res_658_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_651_, v_x_3208__boxed_656_, v_x_3209__boxed_657_, v_x_654_, v_x_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
uint64_t v___x_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
v___x_662_ = l_Lean_instHashableMVarId_hash(v_x_660_);
v___x_663_ = lean_uint64_to_usize(v___x_662_);
v___x_664_ = ((size_t)1ULL);
v___x_665_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_659_, v___x_663_, v___x_664_, v_x_660_, v_x_661_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(lean_object* v_mvarId_666_, lean_object* v_val_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; lean_object* v_mctx_671_; lean_object* v_cache_672_; lean_object* v_zetaDeltaFVarIds_673_; lean_object* v_postponed_674_; lean_object* v_diag_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_704_; 
v___x_670_ = lean_st_ref_take(v___y_668_);
v_mctx_671_ = lean_ctor_get(v___x_670_, 0);
v_cache_672_ = lean_ctor_get(v___x_670_, 1);
v_zetaDeltaFVarIds_673_ = lean_ctor_get(v___x_670_, 2);
v_postponed_674_ = lean_ctor_get(v___x_670_, 3);
v_diag_675_ = lean_ctor_get(v___x_670_, 4);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_704_ == 0)
{
v___x_677_ = v___x_670_;
v_isShared_678_ = v_isSharedCheck_704_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_diag_675_);
lean_inc(v_postponed_674_);
lean_inc(v_zetaDeltaFVarIds_673_);
lean_inc(v_cache_672_);
lean_inc(v_mctx_671_);
lean_dec(v___x_670_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_704_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_depth_679_; lean_object* v_levelAssignDepth_680_; lean_object* v_lmvarCounter_681_; lean_object* v_mvarCounter_682_; lean_object* v_lDecls_683_; lean_object* v_decls_684_; lean_object* v_userNames_685_; lean_object* v_lAssignment_686_; lean_object* v_eAssignment_687_; lean_object* v_dAssignment_688_; lean_object* v_instanceTypedMVars_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_703_; 
v_depth_679_ = lean_ctor_get(v_mctx_671_, 0);
v_levelAssignDepth_680_ = lean_ctor_get(v_mctx_671_, 1);
v_lmvarCounter_681_ = lean_ctor_get(v_mctx_671_, 2);
v_mvarCounter_682_ = lean_ctor_get(v_mctx_671_, 3);
v_lDecls_683_ = lean_ctor_get(v_mctx_671_, 4);
v_decls_684_ = lean_ctor_get(v_mctx_671_, 5);
v_userNames_685_ = lean_ctor_get(v_mctx_671_, 6);
v_lAssignment_686_ = lean_ctor_get(v_mctx_671_, 7);
v_eAssignment_687_ = lean_ctor_get(v_mctx_671_, 8);
v_dAssignment_688_ = lean_ctor_get(v_mctx_671_, 9);
v_instanceTypedMVars_689_ = lean_ctor_get(v_mctx_671_, 10);
v_isSharedCheck_703_ = !lean_is_exclusive(v_mctx_671_);
if (v_isSharedCheck_703_ == 0)
{
v___x_691_ = v_mctx_671_;
v_isShared_692_ = v_isSharedCheck_703_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_instanceTypedMVars_689_);
lean_inc(v_dAssignment_688_);
lean_inc(v_eAssignment_687_);
lean_inc(v_lAssignment_686_);
lean_inc(v_userNames_685_);
lean_inc(v_decls_684_);
lean_inc(v_lDecls_683_);
lean_inc(v_mvarCounter_682_);
lean_inc(v_lmvarCounter_681_);
lean_inc(v_levelAssignDepth_680_);
lean_inc(v_depth_679_);
lean_dec(v_mctx_671_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_703_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_693_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_eAssignment_687_, v_mvarId_666_, v_val_667_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 8, v___x_693_);
v___x_695_ = v___x_691_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_depth_679_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_levelAssignDepth_680_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_lmvarCounter_681_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_mvarCounter_682_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_lDecls_683_);
lean_ctor_set(v_reuseFailAlloc_702_, 5, v_decls_684_);
lean_ctor_set(v_reuseFailAlloc_702_, 6, v_userNames_685_);
lean_ctor_set(v_reuseFailAlloc_702_, 7, v_lAssignment_686_);
lean_ctor_set(v_reuseFailAlloc_702_, 8, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_702_, 9, v_dAssignment_688_);
lean_ctor_set(v_reuseFailAlloc_702_, 10, v_instanceTypedMVars_689_);
v___x_695_ = v_reuseFailAlloc_702_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_697_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_695_);
v___x_697_ = v___x_677_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_cache_672_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_zetaDeltaFVarIds_673_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_postponed_674_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_diag_675_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_st_ref_put(v___y_668_, v___x_697_);
v___x_699_ = lean_box(0);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg___boxed(lean_object* v_mvarId_705_, lean_object* v_val_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_705_, v_val_706_, v___y_707_);
lean_dec(v___y_707_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0(lean_object* v_mvarId_710_, lean_object* v_rule_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; 
lean_inc(v_mvarId_710_);
v___x_719_ = l_Lean_MVarId_getDecl(v_mvarId_710_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v_expr_721_; lean_object* v_pattern_722_; lean_object* v_resultPos_723_; lean_object* v_type_724_; uint8_t v___x_725_; lean_object* v___x_726_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
v_expr_721_ = lean_ctor_get(v_rule_711_, 0);
lean_inc_ref(v_expr_721_);
v_pattern_722_ = lean_ctor_get(v_rule_711_, 1);
lean_inc_ref_n(v_pattern_722_, 2);
v_resultPos_723_ = lean_ctor_get(v_rule_711_, 2);
lean_inc(v_resultPos_723_);
lean_dec_ref(v_rule_711_);
v_type_724_ = lean_ctor_get(v_a_720_, 2);
lean_inc_ref(v_type_724_);
lean_dec(v_a_720_);
v___x_725_ = 1;
v___x_726_ = l_Lean_Meta_Sym_Pattern_unify_x3f(v_pattern_722_, v_type_724_, v___x_725_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_763_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_763_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_763_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_763_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
if (lean_obj_tag(v_a_727_) == 1)
{
lean_object* v_val_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_758_; 
v_val_731_ = lean_ctor_get(v_a_727_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v_a_727_);
if (v_isSharedCheck_758_ == 0)
{
v___x_733_ = v_a_727_;
v_isShared_734_ = v_isSharedCheck_758_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_val_731_);
lean_dec(v_a_727_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_758_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_unresolvedInsts_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_unresolvedInsts_735_ = lean_ctor_get(v_val_731_, 2);
v___x_736_ = lean_array_get_size(v_unresolvedInsts_735_);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_nat_dec_eq(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_741_; 
lean_del_object(v___x_733_);
lean_dec(v_val_731_);
lean_dec(v_resultPos_723_);
lean_dec_ref(v_pattern_722_);
lean_dec_ref(v_expr_721_);
lean_dec(v_mvarId_710_);
v___x_739_ = lean_box(0);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_739_);
v___x_741_ = v___x_729_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_756_; 
lean_del_object(v___x_729_);
lean_inc(v_val_731_);
v___x_743_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(v_expr_721_, v_pattern_722_, v_val_731_);
v___x_744_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_710_, v___x_743_, v___y_715_);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v___x_744_, 0);
lean_dec(v_unused_757_);
v___x_746_ = v___x_744_;
v_isShared_747_ = v_isSharedCheck_756_;
goto v_resetjp_745_;
}
else
{
lean_dec(v___x_744_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_756_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_748_ = lean_box(0);
v___x_749_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(v_val_731_, v_resultPos_723_, v___x_748_);
lean_dec(v_val_731_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_749_);
v___x_751_ = v___x_733_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_755_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_753_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_751_);
v___x_753_ = v___x_746_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
}
else
{
lean_object* v___x_759_; lean_object* v___x_761_; 
lean_dec(v_a_727_);
lean_dec(v_resultPos_723_);
lean_dec_ref(v_pattern_722_);
lean_dec_ref(v_expr_721_);
lean_dec(v_mvarId_710_);
v___x_759_ = lean_box(0);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_759_);
v___x_761_ = v___x_729_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v_resultPos_723_);
lean_dec_ref(v_pattern_722_);
lean_dec_ref(v_expr_721_);
lean_dec(v_mvarId_710_);
v_a_764_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_726_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_726_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v_rule_711_);
lean_dec(v_mvarId_710_);
v_a_772_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_719_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_719_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed(lean_object* v_mvarId_780_, lean_object* v_rule_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Meta_Sym_BackwardRule_apply___lam__0(v_mvarId_780_, v_rule_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object* v_mvarId_790_, lean_object* v_rule_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___f_799_; lean_object* v___x_800_; 
lean_inc(v_mvarId_790_);
v___f_799_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed), 9, 2);
lean_closure_set(v___f_799_, 0, v_mvarId_790_);
lean_closure_set(v___f_799_, 1, v_rule_791_);
v___x_800_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_790_, v___f_799_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___boxed(lean_object* v_mvarId_801_, lean_object* v_rule_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_801_, v_rule_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(lean_object* v_mvarId_811_, lean_object* v_val_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_811_, v_val_812_, v___y_816_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___boxed(lean_object* v_mvarId_821_, lean_object* v_val_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(v_mvarId_821_, v_val_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0(lean_object* v_00_u03b2_831_, lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_x_832_, v_x_833_, v_x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_836_, lean_object* v_x_837_, size_t v_x_838_, size_t v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_837_, v_x_838_, v_x_839_, v_x_840_, v_x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
size_t v_x_3595__boxed_849_; size_t v_x_3596__boxed_850_; lean_object* v_res_851_; 
v_x_3595__boxed_849_ = lean_unbox_usize(v_x_845_);
lean_dec(v_x_845_);
v_x_3596__boxed_850_ = lean_unbox_usize(v_x_846_);
lean_dec(v_x_846_);
v_res_851_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(v_00_u03b2_843_, v_x_844_, v_x_3595__boxed_849_, v_x_3596__boxed_850_, v_x_847_, v_x_848_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_852_, lean_object* v_n_853_, lean_object* v_k_854_, lean_object* v_v_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v_n_853_, v_k_854_, v_v_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_857_, size_t v_depth_858_, lean_object* v_keys_859_, lean_object* v_vals_860_, lean_object* v_heq_861_, lean_object* v_i_862_, lean_object* v_entries_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_858_, v_keys_859_, v_vals_860_, v_i_862_, v_entries_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_865_, lean_object* v_depth_866_, lean_object* v_keys_867_, lean_object* v_vals_868_, lean_object* v_heq_869_, lean_object* v_i_870_, lean_object* v_entries_871_){
_start:
{
size_t v_depth_boxed_872_; lean_object* v_res_873_; 
v_depth_boxed_872_ = lean_unbox_usize(v_depth_866_);
lean_dec(v_depth_866_);
v_res_873_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_865_, v_depth_boxed_872_, v_keys_867_, v_vals_868_, v_heq_869_, v_i_870_, v_entries_871_);
lean_dec_ref(v_vals_868_);
lean_dec_ref(v_keys_867_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_875_, v_x_876_, v_x_877_, v_x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(lean_object* v_msgData_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; lean_object* v_env_887_; lean_object* v___x_888_; lean_object* v_mctx_889_; lean_object* v_lctx_890_; lean_object* v_options_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_886_ = lean_st_ref_get(v___y_884_);
v_env_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc_ref(v_env_887_);
lean_dec(v___x_886_);
v___x_888_ = lean_st_ref_get(v___y_882_);
v_mctx_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc_ref(v_mctx_889_);
lean_dec(v___x_888_);
v_lctx_890_ = lean_ctor_get(v___y_881_, 2);
v_options_891_ = lean_ctor_get(v___y_883_, 2);
lean_inc_ref(v_options_891_);
lean_inc_ref(v_lctx_890_);
v___x_892_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_892_, 0, v_env_887_);
lean_ctor_set(v___x_892_, 1, v_mctx_889_);
lean_ctor_set(v___x_892_, 2, v_lctx_890_);
lean_ctor_set(v___x_892_, 3, v_options_891_);
v___x_893_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v_msgData_880_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0___boxed(lean_object* v_msgData_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msgData_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(lean_object* v_msg_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_ref_908_; lean_object* v___x_909_; lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
v_ref_908_ = lean_ctor_get(v___y_905_, 5);
v___x_909_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msg_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_918_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
lean_inc(v_ref_908_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v_ref_908_);
lean_ctor_set(v___x_914_, 1, v_a_910_);
if (v_isShared_913_ == 0)
{
lean_ctor_set_tag(v___x_912_, 1);
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg___boxed(lean_object* v_msg_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v_msg_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_925_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = ((lean_object*)(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0));
v___x_928_ = l_Lean_stringToMessageData(v___x_927_);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2));
v___x_931_ = l_Lean_stringToMessageData(v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27(lean_object* v_mvarId_932_, lean_object* v_rule_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_941_; 
lean_inc_ref(v_rule_933_);
lean_inc(v_mvarId_932_);
v___x_941_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_932_, v_rule_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_959_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_959_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_959_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_959_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
if (lean_obj_tag(v_a_942_) == 1)
{
lean_object* v_mvarIds_946_; lean_object* v___x_948_; 
lean_dec_ref(v_rule_933_);
lean_dec(v_mvarId_932_);
v_mvarIds_946_ = lean_ctor_get(v_a_942_, 0);
lean_inc(v_mvarIds_946_);
lean_dec_ref_known(v_a_942_, 1);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v_mvarIds_946_);
v___x_948_ = v___x_944_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_mvarIds_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
else
{
lean_object* v_expr_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
lean_del_object(v___x_944_);
lean_dec(v_a_942_);
v_expr_950_ = lean_ctor_get(v_rule_933_, 0);
lean_inc_ref(v_expr_950_);
lean_dec_ref(v_rule_933_);
v___x_951_ = lean_obj_once(&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1, &l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1_once, _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1);
v___x_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_952_, 0, v_mvarId_932_);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_obj_once(&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3, &l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3_once, _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = l_Lean_indentExpr(v_expr_950_);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v___x_957_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
return v___x_958_;
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec_ref(v_rule_933_);
lean_dec(v_mvarId_932_);
v_a_960_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_941_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_941_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___boxed(lean_object* v_mvarId_968_, lean_object* v_rule_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Meta_Sym_BackwardRule_apply_x27(v_mvarId_968_, v_rule_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(lean_object* v_00_u03b1_978_, lean_object* v_msg_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v_msg_979_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___boxed(lean_object* v_00_u03b1_988_, lean_object* v_msg_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(v_00_u03b1_988_, v_msg_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_997_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Apply(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Apply(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Apply(builtin);
}
#ifdef __cplusplus
}
#endif
