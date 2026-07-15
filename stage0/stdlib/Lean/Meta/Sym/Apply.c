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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
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
static const lean_array_object l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3;
static const lean_ctor_object l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2_value),((lean_object*)&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4_value;
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
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_box(0);
v___x_166_ = lean_unsigned_to_nat(16u);
v___x_167_ = lean_mk_array(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_173_ = ((lean_object*)(l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2));
v___x_174_ = lean_box(1);
v___x_175_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1);
v___x_176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
lean_ctor_set(v___x_176_, 2, v___x_173_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(lean_object* v_pattern_179_){
_start:
{
lean_object* v_varTypes_180_; lean_object* v_varInfos_x3f_181_; lean_object* v_pattern_182_; lean_object* v_numArgs_183_; lean_object* v___y_185_; 
v_varTypes_180_ = lean_ctor_get(v_pattern_179_, 1);
lean_inc_ref(v_varTypes_180_);
v_varInfos_x3f_181_ = lean_ctor_get(v_pattern_179_, 2);
lean_inc(v_varInfos_x3f_181_);
v_pattern_182_ = lean_ctor_get(v_pattern_179_, 3);
lean_inc_ref(v_pattern_182_);
lean_dec_ref(v_pattern_179_);
v_numArgs_183_ = lean_array_get_size(v_varTypes_180_);
if (lean_obj_tag(v_varInfos_x3f_181_) == 1)
{
lean_object* v_val_203_; size_t v_sz_204_; size_t v___x_205_; lean_object* v___x_206_; 
v_val_203_ = lean_ctor_get(v_varInfos_x3f_181_, 0);
lean_inc(v_val_203_);
lean_dec_ref_known(v_varInfos_x3f_181_, 1);
v_sz_204_ = lean_array_size(v_val_203_);
v___x_205_ = ((size_t)0ULL);
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(v_sz_204_, v___x_205_, v_val_203_);
v___y_185_ = v___x_206_;
goto v___jp_184_;
}
else
{
uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec(v_varInfos_x3f_181_);
v___x_207_ = 0;
v___x_208_ = lean_box(v___x_207_);
v___x_209_ = lean_mk_array(v_numArgs_183_, v___x_208_);
v___y_185_ = v___x_209_;
goto v___jp_184_;
}
v___jp_184_:
{
size_t v_sz_186_; size_t v___x_187_; lean_object* v_auxVars_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v_fvarIds_193_; size_t v_sz_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_fst_199_; lean_object* v_snd_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_sz_186_ = lean_array_size(v_varTypes_180_);
v___x_187_ = ((size_t)0ULL);
lean_inc_ref(v_varTypes_180_);
v_auxVars_188_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_sz_186_, v___x_187_, v_varTypes_180_);
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3);
v___x_191_ = lean_expr_instantiate_rev(v_pattern_182_, v_auxVars_188_);
lean_dec_ref(v_pattern_182_);
v___x_192_ = l_Lean_collectFVars(v___x_190_, v___x_191_);
v_fvarIds_193_ = lean_ctor_get(v___x_192_, 2);
lean_inc_ref(v_fvarIds_193_);
lean_dec_ref(v___x_192_);
v_sz_194_ = lean_array_size(v_fvarIds_193_);
v___x_195_ = ((lean_object*)(l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4));
v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(v_fvarIds_193_, v_sz_194_, v___x_187_, v___y_185_);
lean_dec_ref(v_fvarIds_193_);
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_188_, v_sz_186_, v___x_187_, v_varTypes_180_);
v___x_198_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_numArgs_183_, v___x_196_, v_numArgs_183_, v_auxVars_188_, v___x_197_, v___x_189_, v___x_195_);
lean_dec_ref(v___x_197_);
lean_dec_ref(v_auxVars_188_);
lean_dec_ref(v___x_196_);
v_fst_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_fst_199_);
v_snd_200_ = lean_ctor_get(v___x_198_, 1);
lean_inc(v_snd_200_);
lean_dec_ref(v___x_198_);
v___x_201_ = l_Array_append___redArg(v_snd_200_, v_fst_199_);
lean_dec(v_fst_199_);
v___x_202_ = lean_array_to_list(v___x_201_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(lean_object* v_as_210_, size_t v_sz_211_, size_t v_i_212_, lean_object* v_bs_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_sz_211_, v_i_212_, v_bs_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___boxed(lean_object* v_as_215_, lean_object* v_sz_216_, lean_object* v_i_217_, lean_object* v_bs_218_){
_start:
{
size_t v_sz_boxed_219_; size_t v_i_boxed_220_; lean_object* v_res_221_; 
v_sz_boxed_219_ = lean_unbox_usize(v_sz_216_);
lean_dec(v_sz_216_);
v_i_boxed_220_ = lean_unbox_usize(v_i_217_);
lean_dec(v_i_217_);
v_res_221_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(v_as_215_, v_sz_boxed_219_, v_i_boxed_220_, v_bs_218_);
lean_dec_ref(v_as_215_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(lean_object* v_auxVars_222_, lean_object* v_as_223_, size_t v_sz_224_, size_t v_i_225_, lean_object* v_bs_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_222_, v_sz_224_, v_i_225_, v_bs_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___boxed(lean_object* v_auxVars_228_, lean_object* v_as_229_, lean_object* v_sz_230_, lean_object* v_i_231_, lean_object* v_bs_232_){
_start:
{
size_t v_sz_boxed_233_; size_t v_i_boxed_234_; lean_object* v_res_235_; 
v_sz_boxed_233_ = lean_unbox_usize(v_sz_230_);
lean_dec(v_sz_230_);
v_i_boxed_234_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_res_235_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(v_auxVars_228_, v_as_229_, v_sz_boxed_233_, v_i_boxed_234_, v_bs_232_);
lean_dec_ref(v_as_229_);
lean_dec_ref(v_auxVars_228_);
return v_res_235_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(lean_object* v_upperBound_236_, lean_object* v___x_237_, lean_object* v___x_238_, lean_object* v___x_239_, lean_object* v_inst_240_, lean_object* v_R_241_, lean_object* v_a_242_, uint8_t v_b_243_, lean_object* v_c_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_upperBound_236_, v___x_237_, v___x_238_, v___x_239_, v_a_242_, v_b_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___boxed(lean_object* v_upperBound_246_, lean_object* v___x_247_, lean_object* v___x_248_, lean_object* v___x_249_, lean_object* v_inst_250_, lean_object* v_R_251_, lean_object* v_a_252_, lean_object* v_b_253_, lean_object* v_c_254_){
_start:
{
uint8_t v_b_boxed_255_; uint8_t v_res_256_; lean_object* v_r_257_; 
v_b_boxed_255_ = lean_unbox(v_b_253_);
v_res_256_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(v_upperBound_246_, v___x_247_, v___x_248_, v___x_249_, v_inst_250_, v_R_251_, v_a_252_, v_b_boxed_255_, v_c_254_);
lean_dec_ref(v___x_249_);
lean_dec_ref(v___x_248_);
lean_dec_ref(v___x_247_);
lean_dec(v_upperBound_246_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(lean_object* v_upperBound_258_, lean_object* v___x_259_, lean_object* v_numArgs_260_, lean_object* v_auxVars_261_, lean_object* v___x_262_, lean_object* v_inst_263_, lean_object* v_R_264_, lean_object* v_a_265_, lean_object* v_b_266_, lean_object* v_c_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_upperBound_258_, v___x_259_, v_numArgs_260_, v_auxVars_261_, v___x_262_, v_a_265_, v_b_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___boxed(lean_object* v_upperBound_269_, lean_object* v___x_270_, lean_object* v_numArgs_271_, lean_object* v_auxVars_272_, lean_object* v___x_273_, lean_object* v_inst_274_, lean_object* v_R_275_, lean_object* v_a_276_, lean_object* v_b_277_, lean_object* v_c_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(v_upperBound_269_, v___x_270_, v_numArgs_271_, v_auxVars_272_, v___x_273_, v_inst_274_, v_R_275_, v_a_276_, v_b_277_, v_c_278_);
lean_dec_ref(v___x_273_);
lean_dec_ref(v_auxVars_272_);
lean_dec(v_numArgs_271_);
lean_dec_ref(v___x_270_);
lean_dec(v_upperBound_269_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object* v_declName_280_, lean_object* v_num_x3f_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v___x_287_; 
lean_inc(v_declName_280_);
v___x_287_ = l_Lean_Meta_Sym_mkPatternFromDecl(v_declName_280_, v_num_x3f_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_299_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_299_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_299_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_299_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
lean_inc(v_a_288_);
v___x_292_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(v_a_288_);
v___x_293_ = lean_box(0);
v___x_294_ = l_Lean_mkConst(v_declName_280_, v___x_293_);
v___x_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v_a_288_);
lean_ctor_set(v___x_295_, 2, v___x_292_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_295_);
v___x_297_ = v___x_290_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec(v_declName_280_);
v_a_300_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_287_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_287_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl___boxed(lean_object* v_declName_308_, lean_object* v_num_x3f_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v_declName_308_, v_num_x3f_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_num_x3f_309_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
if (lean_obj_tag(v_a_316_) == 0)
{
lean_object* v___x_318_; 
v___x_318_ = l_List_reverse___redArg(v_a_317_);
return v___x_318_;
}
else
{
lean_object* v_head_319_; lean_object* v_tail_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_329_; 
v_head_319_ = lean_ctor_get(v_a_316_, 0);
v_tail_320_ = lean_ctor_get(v_a_316_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_a_316_);
if (v_isSharedCheck_329_ == 0)
{
v___x_322_ = v_a_316_;
v_isShared_323_ = v_isSharedCheck_329_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_tail_320_);
lean_inc(v_head_319_);
lean_dec(v_a_316_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_329_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_324_ = l_Lean_mkLevelParam(v_head_319_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v_a_317_);
lean_ctor_set(v___x_322_, 0, v___x_324_);
v___x_326_ = v___x_322_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_a_317_);
v___x_326_ = v_reuseFailAlloc_328_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
v_a_316_ = v_tail_320_;
v_a_317_ = v___x_326_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object* v_e_330_, lean_object* v_levelParams_331_, lean_object* v_num_x3f_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_338_; 
lean_inc(v_levelParams_331_);
lean_inc_ref(v_e_330_);
v___x_338_ = l_Lean_Meta_Sym_mkPatternFromExpr(v_e_330_, v_levelParams_331_, v_num_x3f_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_352_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_352_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_352_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_352_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v_levelParams_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v_levelParams_343_ = lean_ctor_get(v_a_339_, 0);
lean_inc(v_a_339_);
v___x_344_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(v_a_339_);
v___x_345_ = lean_box(0);
lean_inc(v_levelParams_343_);
v___x_346_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(v_levelParams_343_, v___x_345_);
v___x_347_ = l_Lean_Expr_instantiateLevelParams(v_e_330_, v_levelParams_331_, v___x_346_);
lean_dec_ref(v_e_330_);
v___x_348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v_a_339_);
lean_ctor_set(v___x_348_, 2, v___x_344_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_348_);
v___x_350_ = v___x_341_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec(v_levelParams_331_);
lean_dec_ref(v_e_330_);
v_a_353_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_338_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_338_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr___boxed(lean_object* v_e_361_, lean_object* v_levelParams_362_, lean_object* v_num_x3f_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_e_361_, v_levelParams_362_, v_num_x3f_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_num_x3f_363_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(lean_object* v_expr_370_, lean_object* v_pattern_371_, lean_object* v_result_372_){
_start:
{
if (lean_obj_tag(v_expr_370_) == 4)
{
lean_object* v_us_379_; 
v_us_379_ = lean_ctor_get(v_expr_370_, 1);
if (lean_obj_tag(v_us_379_) == 0)
{
lean_object* v_declName_380_; lean_object* v_us_381_; lean_object* v_args_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec_ref(v_pattern_371_);
v_declName_380_ = lean_ctor_get(v_expr_370_, 0);
lean_inc(v_declName_380_);
lean_dec_ref_known(v_expr_370_, 2);
v_us_381_ = lean_ctor_get(v_result_372_, 0);
lean_inc(v_us_381_);
v_args_382_ = lean_ctor_get(v_result_372_, 1);
lean_inc_ref(v_args_382_);
lean_dec_ref(v_result_372_);
v___x_383_ = l_Lean_mkConst(v_declName_380_, v_us_381_);
v___x_384_ = l_Lean_mkAppN(v___x_383_, v_args_382_);
lean_dec_ref(v_args_382_);
return v___x_384_;
}
else
{
goto v___jp_373_;
}
}
else
{
goto v___jp_373_;
}
v___jp_373_:
{
lean_object* v_levelParams_374_; lean_object* v_us_375_; lean_object* v_args_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_levelParams_374_ = lean_ctor_get(v_pattern_371_, 0);
lean_inc(v_levelParams_374_);
lean_dec_ref(v_pattern_371_);
v_us_375_ = lean_ctor_get(v_result_372_, 0);
lean_inc(v_us_375_);
v_args_376_ = lean_ctor_get(v_result_372_, 1);
lean_inc_ref(v_args_376_);
lean_dec_ref(v_result_372_);
v___x_377_ = l_Lean_Expr_instantiateLevelParams(v_expr_370_, v_levelParams_374_, v_us_375_);
lean_dec_ref(v_expr_370_);
v___x_378_ = l_Lean_mkAppN(v___x_377_, v_args_376_);
lean_dec_ref(v_args_376_);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx(lean_object* v_x_385_){
_start:
{
if (lean_obj_tag(v_x_385_) == 0)
{
lean_object* v___x_386_; 
v___x_386_ = lean_unsigned_to_nat(0u);
return v___x_386_;
}
else
{
lean_object* v___x_387_; 
v___x_387_ = lean_unsigned_to_nat(1u);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___boxed(lean_object* v_x_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_Sym_ApplyResult_ctorIdx(v_x_388_);
lean_dec(v_x_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(lean_object* v_t_390_, lean_object* v_k_391_){
_start:
{
if (lean_obj_tag(v_t_390_) == 0)
{
return v_k_391_;
}
else
{
lean_object* v_mvarIds_392_; lean_object* v___x_393_; 
v_mvarIds_392_ = lean_ctor_get(v_t_390_, 0);
lean_inc(v_mvarIds_392_);
lean_dec_ref_known(v_t_390_, 1);
v___x_393_ = lean_apply_1(v_k_391_, v_mvarIds_392_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim(lean_object* v_motive_394_, lean_object* v_ctorIdx_395_, lean_object* v_t_396_, lean_object* v_h_397_, lean_object* v_k_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_396_, v_k_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___boxed(lean_object* v_motive_400_, lean_object* v_ctorIdx_401_, lean_object* v_t_402_, lean_object* v_h_403_, lean_object* v_k_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_Sym_ApplyResult_ctorElim(v_motive_400_, v_ctorIdx_401_, v_t_402_, v_h_403_, v_k_404_);
lean_dec(v_ctorIdx_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim___redArg(lean_object* v_t_406_, lean_object* v_failed_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_406_, v_failed_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim(lean_object* v_motive_409_, lean_object* v_t_410_, lean_object* v_h_411_, lean_object* v_failed_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_410_, v_failed_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim___redArg(lean_object* v_t_414_, lean_object* v_goals_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_414_, v_goals_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim(lean_object* v_motive_417_, lean_object* v_t_418_, lean_object* v_h_419_, lean_object* v_goals_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_418_, v_goals_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(lean_object* v_x_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; 
lean_inc(v___y_424_);
lean_inc_ref(v___y_423_);
v___x_430_ = lean_apply_7(v_x_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, lean_box(0));
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed(lean_object* v_x_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(v_x_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(lean_object* v_mvarId_440_, lean_object* v_x_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___f_449_; lean_object* v___x_450_; 
lean_inc(v___y_443_);
lean_inc_ref(v___y_442_);
v___f_449_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_449_, 0, v_x_441_);
lean_closure_set(v___f_449_, 1, v___y_442_);
lean_closure_set(v___f_449_, 2, v___y_443_);
v___x_450_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_440_, v___f_449_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_450_) == 0)
{
return v___x_450_;
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___boxed(lean_object* v_mvarId_459_, lean_object* v_x_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_459_, v_x_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(lean_object* v_00_u03b1_469_, lean_object* v_mvarId_470_, lean_object* v_x_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_470_, v_x_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___boxed(lean_object* v_00_u03b1_480_, lean_object* v_mvarId_481_, lean_object* v_x_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(v_00_u03b1_480_, v_mvarId_481_, v_x_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(lean_object* v_val_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
if (lean_obj_tag(v_a_492_) == 0)
{
lean_object* v___x_494_; 
v___x_494_ = l_List_reverse___redArg(v_a_493_);
return v___x_494_;
}
else
{
lean_object* v_head_495_; lean_object* v_tail_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_508_; 
v_head_495_ = lean_ctor_get(v_a_492_, 0);
v_tail_496_ = lean_ctor_get(v_a_492_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_a_492_);
if (v_isSharedCheck_508_ == 0)
{
v___x_498_ = v_a_492_;
v_isShared_499_ = v_isSharedCheck_508_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_tail_496_);
lean_inc(v_head_495_);
lean_dec(v_a_492_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_508_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v_args_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v_args_500_ = lean_ctor_get(v_val_491_, 1);
v___x_501_ = l_Lean_instInhabitedExpr;
v___x_502_ = lean_array_get_borrowed(v___x_501_, v_args_500_, v_head_495_);
lean_dec(v_head_495_);
v___x_503_ = l_Lean_Expr_mvarId_x21(v___x_502_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v_a_493_);
lean_ctor_set(v___x_498_, 0, v___x_503_);
v___x_505_ = v___x_498_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_a_493_);
v___x_505_ = v_reuseFailAlloc_507_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
v_a_492_ = v_tail_496_;
v_a_493_ = v___x_505_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1___boxed(lean_object* v_val_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(v_val_509_, v_a_510_, v_a_511_);
lean_dec_ref(v_val_509_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
lean_object* v_ks_517_; lean_object* v_vs_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_542_; 
v_ks_517_ = lean_ctor_get(v_x_513_, 0);
v_vs_518_ = lean_ctor_get(v_x_513_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_x_513_);
if (v_isSharedCheck_542_ == 0)
{
v___x_520_ = v_x_513_;
v_isShared_521_ = v_isSharedCheck_542_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_vs_518_);
lean_inc(v_ks_517_);
lean_dec(v_x_513_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_542_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = lean_array_get_size(v_ks_517_);
v___x_523_ = lean_nat_dec_lt(v_x_514_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
lean_dec(v_x_514_);
v___x_524_ = lean_array_push(v_ks_517_, v_x_515_);
v___x_525_ = lean_array_push(v_vs_518_, v_x_516_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v___x_525_);
lean_ctor_set(v___x_520_, 0, v___x_524_);
v___x_527_ = v___x_520_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_object* v_k_x27_529_; uint8_t v___x_530_; 
v_k_x27_529_ = lean_array_fget_borrowed(v_ks_517_, v_x_514_);
v___x_530_ = l_Lean_instBEqMVarId_beq(v_x_515_, v_k_x27_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_532_; 
if (v_isShared_521_ == 0)
{
v___x_532_ = v___x_520_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_ks_517_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_vs_518_);
v___x_532_ = v_reuseFailAlloc_536_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_add(v_x_514_, v___x_533_);
lean_dec(v_x_514_);
v_x_513_ = v___x_532_;
v_x_514_ = v___x_534_;
goto _start;
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_537_ = lean_array_fset(v_ks_517_, v_x_514_, v_x_515_);
v___x_538_ = lean_array_fset(v_vs_518_, v_x_514_, v_x_516_);
lean_dec(v_x_514_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v___x_538_);
lean_ctor_set(v___x_520_, 0, v___x_537_);
v___x_540_ = v___x_520_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_543_, lean_object* v_k_544_, lean_object* v_v_545_){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_543_, v___x_546_, v_k_544_, v_v_545_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(lean_object* v_x_549_, size_t v_x_550_, size_t v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
if (lean_obj_tag(v_x_549_) == 0)
{
lean_object* v_es_554_; size_t v___x_555_; size_t v___x_556_; lean_object* v_j_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v_es_554_ = lean_ctor_get(v_x_549_, 0);
v___x_555_ = ((size_t)31ULL);
v___x_556_ = lean_usize_land(v_x_550_, v___x_555_);
v_j_557_ = lean_usize_to_nat(v___x_556_);
v___x_558_ = lean_array_get_size(v_es_554_);
v___x_559_ = lean_nat_dec_lt(v_j_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_dec(v_j_557_);
lean_dec(v_x_553_);
lean_dec(v_x_552_);
return v_x_549_;
}
else
{
lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_598_; 
lean_inc_ref(v_es_554_);
v_isSharedCheck_598_ = !lean_is_exclusive(v_x_549_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v_x_549_, 0);
lean_dec(v_unused_599_);
v___x_561_ = v_x_549_;
v_isShared_562_ = v_isSharedCheck_598_;
goto v_resetjp_560_;
}
else
{
lean_dec(v_x_549_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_598_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_v_563_; lean_object* v___x_564_; lean_object* v_xs_x27_565_; lean_object* v___y_567_; 
v_v_563_ = lean_array_fget(v_es_554_, v_j_557_);
v___x_564_ = lean_box(0);
v_xs_x27_565_ = lean_array_fset(v_es_554_, v_j_557_, v___x_564_);
switch(lean_obj_tag(v_v_563_))
{
case 0:
{
lean_object* v_key_572_; lean_object* v_val_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_583_; 
v_key_572_ = lean_ctor_get(v_v_563_, 0);
v_val_573_ = lean_ctor_get(v_v_563_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v_v_563_);
if (v_isSharedCheck_583_ == 0)
{
v___x_575_ = v_v_563_;
v_isShared_576_ = v_isSharedCheck_583_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_val_573_);
lean_inc(v_key_572_);
lean_dec(v_v_563_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_583_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
uint8_t v___x_577_; 
v___x_577_ = l_Lean_instBEqMVarId_beq(v_x_552_, v_key_572_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_del_object(v___x_575_);
v___x_578_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_572_, v_val_573_, v_x_552_, v_x_553_);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
v___y_567_ = v___x_579_;
goto v___jp_566_;
}
else
{
lean_object* v___x_581_; 
lean_dec(v_val_573_);
lean_dec(v_key_572_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 1, v_x_553_);
lean_ctor_set(v___x_575_, 0, v_x_552_);
v___x_581_ = v___x_575_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_x_552_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_x_553_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
v___y_567_ = v___x_581_;
goto v___jp_566_;
}
}
}
}
case 1:
{
lean_object* v_node_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_596_; 
v_node_584_ = lean_ctor_get(v_v_563_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v_v_563_);
if (v_isSharedCheck_596_ == 0)
{
v___x_586_ = v_v_563_;
v_isShared_587_ = v_isSharedCheck_596_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_node_584_);
lean_dec(v_v_563_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_596_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
size_t v___x_588_; size_t v___x_589_; size_t v___x_590_; size_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_588_ = ((size_t)5ULL);
v___x_589_ = lean_usize_shift_right(v_x_550_, v___x_588_);
v___x_590_ = ((size_t)1ULL);
v___x_591_ = lean_usize_add(v_x_551_, v___x_590_);
v___x_592_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_node_584_, v___x_589_, v___x_591_, v_x_552_, v_x_553_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_592_);
v___x_594_ = v___x_586_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
v___y_567_ = v___x_594_;
goto v___jp_566_;
}
}
}
default: 
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_x_552_);
lean_ctor_set(v___x_597_, 1, v_x_553_);
v___y_567_ = v___x_597_;
goto v___jp_566_;
}
}
v___jp_566_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = lean_array_fset(v_xs_x27_565_, v_j_557_, v___y_567_);
lean_dec(v_j_557_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_568_);
v___x_570_ = v___x_561_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
else
{
lean_object* v_ks_600_; lean_object* v_vs_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_621_; 
v_ks_600_ = lean_ctor_get(v_x_549_, 0);
v_vs_601_ = lean_ctor_get(v_x_549_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v_x_549_);
if (v_isSharedCheck_621_ == 0)
{
v___x_603_ = v_x_549_;
v_isShared_604_ = v_isSharedCheck_621_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_vs_601_);
lean_inc(v_ks_600_);
lean_dec(v_x_549_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_621_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_ks_600_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_vs_601_);
v___x_606_ = v_reuseFailAlloc_620_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v_newNode_607_; uint8_t v___y_609_; size_t v___x_615_; uint8_t v___x_616_; 
v_newNode_607_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v___x_606_, v_x_552_, v_x_553_);
v___x_615_ = ((size_t)7ULL);
v___x_616_ = lean_usize_dec_le(v___x_615_, v_x_551_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_617_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_607_);
v___x_618_ = lean_unsigned_to_nat(4u);
v___x_619_ = lean_nat_dec_lt(v___x_617_, v___x_618_);
lean_dec(v___x_617_);
v___y_609_ = v___x_619_;
goto v___jp_608_;
}
else
{
v___y_609_ = v___x_616_;
goto v___jp_608_;
}
v___jp_608_:
{
if (v___y_609_ == 0)
{
lean_object* v_ks_610_; lean_object* v_vs_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_ks_610_ = lean_ctor_get(v_newNode_607_, 0);
lean_inc_ref(v_ks_610_);
v_vs_611_ = lean_ctor_get(v_newNode_607_, 1);
lean_inc_ref(v_vs_611_);
lean_dec_ref(v_newNode_607_);
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_614_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_x_551_, v_ks_610_, v_vs_611_, v___x_612_, v___x_613_);
lean_dec_ref(v_vs_611_);
lean_dec_ref(v_ks_610_);
return v___x_614_;
}
else
{
return v_newNode_607_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_622_, lean_object* v_keys_623_, lean_object* v_vals_624_, lean_object* v_i_625_, lean_object* v_entries_626_){
_start:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_array_get_size(v_keys_623_);
v___x_628_ = lean_nat_dec_lt(v_i_625_, v___x_627_);
if (v___x_628_ == 0)
{
lean_dec(v_i_625_);
return v_entries_626_;
}
else
{
lean_object* v_k_629_; lean_object* v_v_630_; uint64_t v___x_631_; size_t v_h_632_; size_t v___x_633_; lean_object* v___x_634_; size_t v___x_635_; size_t v___x_636_; size_t v___x_637_; size_t v_h_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_k_629_ = lean_array_fget_borrowed(v_keys_623_, v_i_625_);
v_v_630_ = lean_array_fget_borrowed(v_vals_624_, v_i_625_);
v___x_631_ = l_Lean_instHashableMVarId_hash(v_k_629_);
v_h_632_ = lean_uint64_to_usize(v___x_631_);
v___x_633_ = ((size_t)5ULL);
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = ((size_t)1ULL);
v___x_636_ = lean_usize_sub(v_depth_622_, v___x_635_);
v___x_637_ = lean_usize_mul(v___x_633_, v___x_636_);
v_h_638_ = lean_usize_shift_right(v_h_632_, v___x_637_);
v___x_639_ = lean_nat_add(v_i_625_, v___x_634_);
lean_dec(v_i_625_);
lean_inc(v_v_630_);
lean_inc(v_k_629_);
v___x_640_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_entries_626_, v_h_638_, v_depth_622_, v_k_629_, v_v_630_);
v_i_625_ = v___x_639_;
v_entries_626_ = v___x_640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_642_, lean_object* v_keys_643_, lean_object* v_vals_644_, lean_object* v_i_645_, lean_object* v_entries_646_){
_start:
{
size_t v_depth_boxed_647_; lean_object* v_res_648_; 
v_depth_boxed_647_ = lean_unbox_usize(v_depth_642_);
lean_dec(v_depth_642_);
v_res_648_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_647_, v_keys_643_, v_vals_644_, v_i_645_, v_entries_646_);
lean_dec_ref(v_vals_644_);
lean_dec_ref(v_keys_643_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
size_t v_x_3204__boxed_654_; size_t v_x_3205__boxed_655_; lean_object* v_res_656_; 
v_x_3204__boxed_654_ = lean_unbox_usize(v_x_650_);
lean_dec(v_x_650_);
v_x_3205__boxed_655_ = lean_unbox_usize(v_x_651_);
lean_dec(v_x_651_);
v_res_656_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_649_, v_x_3204__boxed_654_, v_x_3205__boxed_655_, v_x_652_, v_x_653_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
uint64_t v___x_660_; size_t v___x_661_; size_t v___x_662_; lean_object* v___x_663_; 
v___x_660_ = l_Lean_instHashableMVarId_hash(v_x_658_);
v___x_661_ = lean_uint64_to_usize(v___x_660_);
v___x_662_ = ((size_t)1ULL);
v___x_663_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_657_, v___x_661_, v___x_662_, v_x_658_, v_x_659_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(lean_object* v_mvarId_664_, lean_object* v_val_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; lean_object* v_mctx_669_; lean_object* v_cache_670_; lean_object* v_zetaDeltaFVarIds_671_; lean_object* v_postponed_672_; lean_object* v_diag_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_701_; 
v___x_668_ = lean_st_ref_take(v___y_666_);
v_mctx_669_ = lean_ctor_get(v___x_668_, 0);
v_cache_670_ = lean_ctor_get(v___x_668_, 1);
v_zetaDeltaFVarIds_671_ = lean_ctor_get(v___x_668_, 2);
v_postponed_672_ = lean_ctor_get(v___x_668_, 3);
v_diag_673_ = lean_ctor_get(v___x_668_, 4);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_701_ == 0)
{
v___x_675_ = v___x_668_;
v_isShared_676_ = v_isSharedCheck_701_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_diag_673_);
lean_inc(v_postponed_672_);
lean_inc(v_zetaDeltaFVarIds_671_);
lean_inc(v_cache_670_);
lean_inc(v_mctx_669_);
lean_dec(v___x_668_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_701_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v_depth_677_; lean_object* v_levelAssignDepth_678_; lean_object* v_lmvarCounter_679_; lean_object* v_mvarCounter_680_; lean_object* v_lDecls_681_; lean_object* v_decls_682_; lean_object* v_userNames_683_; lean_object* v_lAssignment_684_; lean_object* v_eAssignment_685_; lean_object* v_dAssignment_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_700_; 
v_depth_677_ = lean_ctor_get(v_mctx_669_, 0);
v_levelAssignDepth_678_ = lean_ctor_get(v_mctx_669_, 1);
v_lmvarCounter_679_ = lean_ctor_get(v_mctx_669_, 2);
v_mvarCounter_680_ = lean_ctor_get(v_mctx_669_, 3);
v_lDecls_681_ = lean_ctor_get(v_mctx_669_, 4);
v_decls_682_ = lean_ctor_get(v_mctx_669_, 5);
v_userNames_683_ = lean_ctor_get(v_mctx_669_, 6);
v_lAssignment_684_ = lean_ctor_get(v_mctx_669_, 7);
v_eAssignment_685_ = lean_ctor_get(v_mctx_669_, 8);
v_dAssignment_686_ = lean_ctor_get(v_mctx_669_, 9);
v_isSharedCheck_700_ = !lean_is_exclusive(v_mctx_669_);
if (v_isSharedCheck_700_ == 0)
{
v___x_688_ = v_mctx_669_;
v_isShared_689_ = v_isSharedCheck_700_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_dAssignment_686_);
lean_inc(v_eAssignment_685_);
lean_inc(v_lAssignment_684_);
lean_inc(v_userNames_683_);
lean_inc(v_decls_682_);
lean_inc(v_lDecls_681_);
lean_inc(v_mvarCounter_680_);
lean_inc(v_lmvarCounter_679_);
lean_inc(v_levelAssignDepth_678_);
lean_inc(v_depth_677_);
lean_dec(v_mctx_669_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_700_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_eAssignment_685_, v_mvarId_664_, v_val_665_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 8, v___x_690_);
v___x_692_ = v___x_688_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_depth_677_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_levelAssignDepth_678_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_lmvarCounter_679_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v_mvarCounter_680_);
lean_ctor_set(v_reuseFailAlloc_699_, 4, v_lDecls_681_);
lean_ctor_set(v_reuseFailAlloc_699_, 5, v_decls_682_);
lean_ctor_set(v_reuseFailAlloc_699_, 6, v_userNames_683_);
lean_ctor_set(v_reuseFailAlloc_699_, 7, v_lAssignment_684_);
lean_ctor_set(v_reuseFailAlloc_699_, 8, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_699_, 9, v_dAssignment_686_);
v___x_692_ = v_reuseFailAlloc_699_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_692_);
v___x_694_ = v___x_675_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_cache_670_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_zetaDeltaFVarIds_671_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_postponed_672_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_diag_673_);
v___x_694_ = v_reuseFailAlloc_698_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_st_ref_set(v___y_666_, v___x_694_);
v___x_696_ = lean_box(0);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg___boxed(lean_object* v_mvarId_702_, lean_object* v_val_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_702_, v_val_703_, v___y_704_);
lean_dec(v___y_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0(lean_object* v_mvarId_707_, lean_object* v_rule_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
lean_inc(v_mvarId_707_);
v___x_716_ = l_Lean_MVarId_getDecl(v_mvarId_707_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v_expr_718_; lean_object* v_pattern_719_; lean_object* v_resultPos_720_; lean_object* v_type_721_; uint8_t v___x_722_; lean_object* v___x_723_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v_expr_718_ = lean_ctor_get(v_rule_708_, 0);
lean_inc_ref(v_expr_718_);
v_pattern_719_ = lean_ctor_get(v_rule_708_, 1);
lean_inc_ref_n(v_pattern_719_, 2);
v_resultPos_720_ = lean_ctor_get(v_rule_708_, 2);
lean_inc(v_resultPos_720_);
lean_dec_ref(v_rule_708_);
v_type_721_ = lean_ctor_get(v_a_717_, 2);
lean_inc_ref(v_type_721_);
lean_dec(v_a_717_);
v___x_722_ = 1;
v___x_723_ = l_Lean_Meta_Sym_Pattern_unify_x3f(v_pattern_719_, v_type_721_, v___x_722_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_760_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_760_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_760_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_760_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
if (lean_obj_tag(v_a_724_) == 1)
{
lean_object* v_val_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_755_; 
v_val_728_ = lean_ctor_get(v_a_724_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v_a_724_);
if (v_isSharedCheck_755_ == 0)
{
v___x_730_ = v_a_724_;
v_isShared_731_ = v_isSharedCheck_755_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_val_728_);
lean_dec(v_a_724_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_755_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_unresolvedInsts_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_unresolvedInsts_732_ = lean_ctor_get(v_val_728_, 2);
v___x_733_ = lean_array_get_size(v_unresolvedInsts_732_);
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_nat_dec_eq(v___x_733_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_738_; 
lean_del_object(v___x_730_);
lean_dec(v_val_728_);
lean_dec(v_resultPos_720_);
lean_dec_ref(v_pattern_719_);
lean_dec_ref(v_expr_718_);
lean_dec(v_mvarId_707_);
v___x_736_ = lean_box(0);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_736_);
v___x_738_ = v___x_726_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_753_; 
lean_del_object(v___x_726_);
lean_inc(v_val_728_);
v___x_740_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(v_expr_718_, v_pattern_719_, v_val_728_);
v___x_741_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_707_, v___x_740_, v___y_712_);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_753_ == 0)
{
lean_object* v_unused_754_; 
v_unused_754_ = lean_ctor_get(v___x_741_, 0);
lean_dec(v_unused_754_);
v___x_743_ = v___x_741_;
v_isShared_744_ = v_isSharedCheck_753_;
goto v_resetjp_742_;
}
else
{
lean_dec(v___x_741_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_753_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_745_ = lean_box(0);
v___x_746_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(v_val_728_, v_resultPos_720_, v___x_745_);
lean_dec(v_val_728_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_746_);
v___x_748_ = v___x_730_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_752_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_750_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_748_);
v___x_750_ = v___x_743_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_758_; 
lean_dec(v_a_724_);
lean_dec(v_resultPos_720_);
lean_dec_ref(v_pattern_719_);
lean_dec_ref(v_expr_718_);
lean_dec(v_mvarId_707_);
v___x_756_ = lean_box(0);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_756_);
v___x_758_ = v___x_726_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_resultPos_720_);
lean_dec_ref(v_pattern_719_);
lean_dec_ref(v_expr_718_);
lean_dec(v_mvarId_707_);
v_a_761_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_723_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_723_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v_rule_708_);
lean_dec(v_mvarId_707_);
v_a_769_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_716_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_716_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed(lean_object* v_mvarId_777_, lean_object* v_rule_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Meta_Sym_BackwardRule_apply___lam__0(v_mvarId_777_, v_rule_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object* v_mvarId_787_, lean_object* v_rule_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___f_796_; lean_object* v___x_797_; 
lean_inc(v_mvarId_787_);
v___f_796_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed), 9, 2);
lean_closure_set(v___f_796_, 0, v_mvarId_787_);
lean_closure_set(v___f_796_, 1, v_rule_788_);
v___x_797_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_787_, v___f_796_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___boxed(lean_object* v_mvarId_798_, lean_object* v_rule_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_798_, v_rule_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(lean_object* v_mvarId_808_, lean_object* v_val_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_808_, v_val_809_, v___y_813_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___boxed(lean_object* v_mvarId_818_, lean_object* v_val_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(v_mvarId_818_, v_val_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0(lean_object* v_00_u03b2_828_, lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_x_829_, v_x_830_, v_x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_833_, lean_object* v_x_834_, size_t v_x_835_, size_t v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_834_, v_x_835_, v_x_836_, v_x_837_, v_x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
size_t v_x_3591__boxed_846_; size_t v_x_3592__boxed_847_; lean_object* v_res_848_; 
v_x_3591__boxed_846_ = lean_unbox_usize(v_x_842_);
lean_dec(v_x_842_);
v_x_3592__boxed_847_ = lean_unbox_usize(v_x_843_);
lean_dec(v_x_843_);
v_res_848_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(v_00_u03b2_840_, v_x_841_, v_x_3591__boxed_846_, v_x_3592__boxed_847_, v_x_844_, v_x_845_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_849_, lean_object* v_n_850_, lean_object* v_k_851_, lean_object* v_v_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v_n_850_, v_k_851_, v_v_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_854_, size_t v_depth_855_, lean_object* v_keys_856_, lean_object* v_vals_857_, lean_object* v_heq_858_, lean_object* v_i_859_, lean_object* v_entries_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_855_, v_keys_856_, v_vals_857_, v_i_859_, v_entries_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_862_, lean_object* v_depth_863_, lean_object* v_keys_864_, lean_object* v_vals_865_, lean_object* v_heq_866_, lean_object* v_i_867_, lean_object* v_entries_868_){
_start:
{
size_t v_depth_boxed_869_; lean_object* v_res_870_; 
v_depth_boxed_869_ = lean_unbox_usize(v_depth_863_);
lean_dec(v_depth_863_);
v_res_870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_862_, v_depth_boxed_869_, v_keys_864_, v_vals_865_, v_heq_866_, v_i_867_, v_entries_868_);
lean_dec_ref(v_vals_865_);
lean_dec_ref(v_keys_864_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_872_, v_x_873_, v_x_874_, v_x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(lean_object* v_msgData_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; lean_object* v_env_884_; lean_object* v___x_885_; lean_object* v_mctx_886_; lean_object* v_lctx_887_; lean_object* v_options_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_883_ = lean_st_ref_get(v___y_881_);
v_env_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc_ref(v_env_884_);
lean_dec(v___x_883_);
v___x_885_ = lean_st_ref_get(v___y_879_);
v_mctx_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc_ref(v_mctx_886_);
lean_dec(v___x_885_);
v_lctx_887_ = lean_ctor_get(v___y_878_, 2);
v_options_888_ = lean_ctor_get(v___y_880_, 2);
lean_inc_ref(v_options_888_);
lean_inc_ref(v_lctx_887_);
v___x_889_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_889_, 0, v_env_884_);
lean_ctor_set(v___x_889_, 1, v_mctx_886_);
lean_ctor_set(v___x_889_, 2, v_lctx_887_);
lean_ctor_set(v___x_889_, 3, v_options_888_);
v___x_890_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v_msgData_877_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0___boxed(lean_object* v_msgData_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msgData_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(lean_object* v_msg_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_ref_905_; lean_object* v___x_906_; lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_915_; 
v_ref_905_ = lean_ctor_get(v___y_902_, 5);
v___x_906_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msg_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_915_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_915_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_915_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
lean_inc(v_ref_905_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_ref_905_);
lean_ctor_set(v___x_911_, 1, v_a_907_);
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 1);
lean_ctor_set(v___x_909_, 0, v___x_911_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg___boxed(lean_object* v_msg_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v_msg_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_922_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = ((lean_object*)(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0));
v___x_925_ = l_Lean_stringToMessageData(v___x_924_);
return v___x_925_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = ((lean_object*)(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2));
v___x_928_ = l_Lean_stringToMessageData(v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27(lean_object* v_mvarId_929_, lean_object* v_rule_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v___x_938_; 
lean_inc_ref(v_rule_930_);
lean_inc(v_mvarId_929_);
v___x_938_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_929_, v_rule_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_956_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_956_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_956_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_956_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
if (lean_obj_tag(v_a_939_) == 1)
{
lean_object* v_mvarIds_943_; lean_object* v___x_945_; 
lean_dec_ref(v_rule_930_);
lean_dec(v_mvarId_929_);
v_mvarIds_943_ = lean_ctor_get(v_a_939_, 0);
lean_inc(v_mvarIds_943_);
lean_dec_ref_known(v_a_939_, 1);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v_mvarIds_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_mvarIds_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
else
{
lean_object* v_expr_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
lean_del_object(v___x_941_);
lean_dec(v_a_939_);
v_expr_947_ = lean_ctor_get(v_rule_930_, 0);
lean_inc_ref(v_expr_947_);
lean_dec_ref(v_rule_930_);
v___x_948_ = lean_obj_once(&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1, &l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1_once, _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1);
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v_mvarId_929_);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_obj_once(&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3, &l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3_once, _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = l_Lean_indentExpr(v_expr_947_);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v___x_954_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
return v___x_955_;
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec_ref(v_rule_930_);
lean_dec(v_mvarId_929_);
v_a_957_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_938_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_938_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___boxed(lean_object* v_mvarId_965_, lean_object* v_rule_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Meta_Sym_BackwardRule_apply_x27(v_mvarId_965_, v_rule_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(lean_object* v_00_u03b1_975_, lean_object* v_msg_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v_msg_976_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___boxed(lean_object* v_00_u03b1_985_, lean_object* v_msg_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(v_00_u03b1_985_, v_msg_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
return v_res_994_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
