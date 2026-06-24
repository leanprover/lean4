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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_unify_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkPatternFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_mkPatternFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_sym_pre"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 124, 57, 118, 127, 154, 73, 9)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(lean_object* v_auxVars_20_, lean_object* v_as_21_, lean_object* v_i_22_, lean_object* v_j_23_, lean_object* v_bs_24_){
_start:
{
lean_object* v_zero_25_; uint8_t v_isZero_26_; 
v_zero_25_ = lean_unsigned_to_nat(0u);
v_isZero_26_ = lean_nat_dec_eq(v_i_22_, v_zero_25_);
if (v_isZero_26_ == 1)
{
lean_dec(v_j_23_);
lean_dec(v_i_22_);
return v_bs_24_;
}
else
{
lean_object* v_one_27_; lean_object* v_n_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_one_27_ = lean_unsigned_to_nat(1u);
v_n_28_ = lean_nat_sub(v_i_22_, v_one_27_);
lean_dec(v_i_22_);
v___x_29_ = lean_array_fget_borrowed(v_as_21_, v_j_23_);
v___x_30_ = lean_expr_instantiate_rev_range(v___x_29_, v_zero_25_, v_j_23_, v_auxVars_20_);
v___x_31_ = lean_nat_add(v_j_23_, v_one_27_);
lean_dec(v_j_23_);
v___x_32_ = lean_array_push(v_bs_24_, v___x_30_);
v_i_22_ = v_n_28_;
v_j_23_ = v___x_31_;
v_bs_24_ = v___x_32_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg___boxed(lean_object* v_auxVars_34_, lean_object* v_as_35_, lean_object* v_i_36_, lean_object* v_j_37_, lean_object* v_bs_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_34_, v_as_35_, v_i_36_, v_j_37_, v_bs_38_);
lean_dec_ref(v_as_35_);
lean_dec_ref(v_auxVars_34_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(lean_object* v_as_43_, size_t v_sz_44_, size_t v_i_45_, lean_object* v_b_46_){
_start:
{
lean_object* v_a_48_; uint8_t v___x_52_; 
v___x_52_ = lean_usize_dec_lt(v_i_45_, v_sz_44_);
if (v___x_52_ == 0)
{
return v_b_46_;
}
else
{
lean_object* v_a_53_; 
v_a_53_ = lean_array_uget_borrowed(v_as_43_, v_i_45_);
if (lean_obj_tag(v_a_53_) == 2)
{
lean_object* v_pre_54_; lean_object* v_i_55_; lean_object* v_auxPrefix_56_; uint8_t v___x_57_; 
v_pre_54_ = lean_ctor_get(v_a_53_, 0);
v_i_55_ = lean_ctor_get(v_a_53_, 1);
v_auxPrefix_56_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1));
v___x_57_ = lean_name_eq(v_pre_54_, v_auxPrefix_56_);
if (v___x_57_ == 0)
{
v_a_48_ = v_b_46_;
goto v___jp_47_;
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_box(v___x_57_);
v___x_59_ = lean_array_set(v_b_46_, v_i_55_, v___x_58_);
v_a_48_ = v___x_59_;
goto v___jp_47_;
}
}
else
{
v_a_48_ = v_b_46_;
goto v___jp_47_;
}
}
v___jp_47_:
{
size_t v___x_49_; size_t v___x_50_; 
v___x_49_ = ((size_t)1ULL);
v___x_50_ = lean_usize_add(v_i_45_, v___x_49_);
v_i_45_ = v___x_50_;
v_b_46_ = v_a_48_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___boxed(lean_object* v_as_60_, lean_object* v_sz_61_, lean_object* v_i_62_, lean_object* v_b_63_){
_start:
{
size_t v_sz_boxed_64_; size_t v_i_boxed_65_; lean_object* v_res_66_; 
v_sz_boxed_64_ = lean_unbox_usize(v_sz_61_);
lean_dec(v_sz_61_);
v_i_boxed_65_ = lean_unbox_usize(v_i_62_);
lean_dec(v_i_62_);
v_res_66_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(v_as_60_, v_sz_boxed_64_, v_i_boxed_65_, v_b_63_);
lean_dec_ref(v_as_60_);
return v_res_66_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(lean_object* v_upperBound_67_, lean_object* v___x_68_, lean_object* v___x_69_, lean_object* v___x_70_, lean_object* v_a_71_, uint8_t v_b_72_){
_start:
{
uint8_t v_a_74_; uint8_t v___x_78_; 
v___x_78_ = lean_nat_dec_lt(v_a_71_, v_upperBound_67_);
if (v___x_78_ == 0)
{
lean_dec(v_a_71_);
return v_b_72_;
}
else
{
uint8_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_79_ = 0;
v___x_80_ = lean_box(v___x_79_);
v___x_81_ = lean_array_get(v___x_80_, v___x_68_, v_a_71_);
lean_dec(v___x_80_);
v___x_82_ = lean_unbox(v___x_81_);
lean_dec(v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_83_ = l_Lean_instInhabitedExpr;
v___x_84_ = lean_array_get_borrowed(v___x_83_, v___x_69_, v_a_71_);
v___x_85_ = l_Lean_Expr_fvarId_x21(v___x_70_);
v___x_86_ = l_Lean_Expr_containsFVar(v___x_84_, v___x_85_);
lean_dec(v___x_85_);
if (v___x_86_ == 0)
{
v_a_74_ = v_b_72_;
goto v___jp_73_;
}
else
{
lean_dec(v_a_71_);
return v___x_86_;
}
}
else
{
v_a_74_ = v_b_72_;
goto v___jp_73_;
}
}
v___jp_73_:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_add(v_a_71_, v___x_75_);
lean_dec(v_a_71_);
v_a_71_ = v___x_76_;
v_b_72_ = v_a_74_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg___boxed(lean_object* v_upperBound_87_, lean_object* v___x_88_, lean_object* v___x_89_, lean_object* v___x_90_, lean_object* v_a_91_, lean_object* v_b_92_){
_start:
{
uint8_t v_b_boxed_93_; uint8_t v_res_94_; lean_object* v_r_95_; 
v_b_boxed_93_ = lean_unbox(v_b_92_);
v_res_94_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_upperBound_87_, v___x_88_, v___x_89_, v___x_90_, v_a_91_, v_b_boxed_93_);
lean_dec_ref(v___x_90_);
lean_dec_ref(v___x_89_);
lean_dec_ref(v___x_88_);
lean_dec(v_upperBound_87_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(lean_object* v_upperBound_96_, lean_object* v___x_97_, lean_object* v_numArgs_98_, lean_object* v_auxVars_99_, lean_object* v___x_100_, lean_object* v_a_101_, lean_object* v_b_102_){
_start:
{
lean_object* v_a_104_; uint8_t v___x_108_; 
v___x_108_ = lean_nat_dec_lt(v_a_101_, v_upperBound_96_);
if (v___x_108_ == 0)
{
lean_dec(v_a_101_);
return v_b_102_;
}
else
{
lean_object* v_fst_109_; lean_object* v_snd_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_135_; 
v_fst_109_ = lean_ctor_get(v_b_102_, 0);
v_snd_110_ = lean_ctor_get(v_b_102_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_b_102_);
if (v_isSharedCheck_135_ == 0)
{
v___x_112_ = v_b_102_;
v_isShared_113_ = v_isSharedCheck_135_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_snd_110_);
lean_inc(v_fst_109_);
lean_dec(v_b_102_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_135_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_114_ = 0;
v___x_115_ = lean_box(v___x_114_);
v___x_116_ = lean_array_get(v___x_115_, v___x_97_, v_a_101_);
lean_dec(v___x_115_);
v___x_117_ = lean_unbox(v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; uint8_t v___x_123_; 
v___x_118_ = l_Lean_instInhabitedExpr;
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v_a_101_, v___x_119_);
v___x_121_ = lean_array_get_borrowed(v___x_118_, v_auxVars_99_, v_a_101_);
v___x_122_ = lean_unbox(v___x_116_);
lean_dec(v___x_116_);
v___x_123_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_numArgs_98_, v___x_97_, v___x_100_, v___x_121_, v___x_120_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_126_; 
lean_inc(v_a_101_);
v___x_124_ = lean_array_push(v_snd_110_, v_a_101_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 1, v___x_124_);
v___x_126_ = v___x_112_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_fst_109_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
v_a_104_ = v___x_126_;
goto v___jp_103_;
}
}
else
{
lean_object* v___x_128_; lean_object* v___x_130_; 
lean_inc(v_a_101_);
v___x_128_ = lean_array_push(v_fst_109_, v_a_101_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_128_);
v___x_130_ = v___x_112_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_snd_110_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
v_a_104_ = v___x_130_;
goto v___jp_103_;
}
}
}
else
{
lean_object* v___x_133_; 
lean_dec(v___x_116_);
if (v_isShared_113_ == 0)
{
v___x_133_ = v___x_112_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_fst_109_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_snd_110_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
v_a_104_ = v___x_133_;
goto v___jp_103_;
}
}
}
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v_a_101_, v___x_105_);
lean_dec(v_a_101_);
v_a_101_ = v___x_106_;
v_b_102_ = v_a_104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg___boxed(lean_object* v_upperBound_136_, lean_object* v___x_137_, lean_object* v_numArgs_138_, lean_object* v_auxVars_139_, lean_object* v___x_140_, lean_object* v_a_141_, lean_object* v_b_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_upperBound_136_, v___x_137_, v_numArgs_138_, v_auxVars_139_, v___x_140_, v_a_141_, v_b_142_);
lean_dec_ref(v___x_140_);
lean_dec_ref(v_auxVars_139_);
lean_dec(v_numArgs_138_);
lean_dec_ref(v___x_137_);
lean_dec(v_upperBound_136_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(lean_object* v_i_144_, lean_object* v_j_145_, lean_object* v_bs_146_){
_start:
{
lean_object* v_zero_147_; uint8_t v_isZero_148_; 
v_zero_147_ = lean_unsigned_to_nat(0u);
v_isZero_148_ = lean_nat_dec_eq(v_i_144_, v_zero_147_);
if (v_isZero_148_ == 1)
{
lean_dec(v_j_145_);
lean_dec(v_i_144_);
return v_bs_146_;
}
else
{
lean_object* v_auxPrefix_149_; lean_object* v_one_150_; lean_object* v_n_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_auxPrefix_149_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1));
v_one_150_ = lean_unsigned_to_nat(1u);
v_n_151_ = lean_nat_sub(v_i_144_, v_one_150_);
lean_dec(v_i_144_);
lean_inc(v_j_145_);
v___x_152_ = l_Lean_Name_num___override(v_auxPrefix_149_, v_j_145_);
v___x_153_ = l_Lean_mkFVar(v___x_152_);
v___x_154_ = lean_nat_add(v_j_145_, v_one_150_);
lean_dec(v_j_145_);
v___x_155_ = lean_array_push(v_bs_146_, v___x_153_);
v_i_144_ = v_n_151_;
v_j_145_ = v___x_154_;
v_bs_146_ = v___x_155_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_box(0);
v___x_158_ = lean_unsigned_to_nat(16u);
v___x_159_ = lean_mk_array(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = ((lean_object*)(l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2));
v___x_166_ = lean_box(1);
v___x_167_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1);
v___x_168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
lean_ctor_set(v___x_168_, 2, v___x_165_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(lean_object* v_pattern_171_){
_start:
{
lean_object* v_varTypes_172_; lean_object* v_varInfos_x3f_173_; lean_object* v_pattern_174_; lean_object* v_numArgs_175_; lean_object* v___y_177_; 
v_varTypes_172_ = lean_ctor_get(v_pattern_171_, 1);
lean_inc_ref(v_varTypes_172_);
v_varInfos_x3f_173_ = lean_ctor_get(v_pattern_171_, 2);
lean_inc(v_varInfos_x3f_173_);
v_pattern_174_ = lean_ctor_get(v_pattern_171_, 3);
lean_inc_ref(v_pattern_174_);
lean_dec_ref(v_pattern_171_);
v_numArgs_175_ = lean_array_get_size(v_varTypes_172_);
if (lean_obj_tag(v_varInfos_x3f_173_) == 1)
{
lean_object* v_val_195_; size_t v_sz_196_; size_t v___x_197_; lean_object* v___x_198_; 
v_val_195_ = lean_ctor_get(v_varInfos_x3f_173_, 0);
lean_inc(v_val_195_);
lean_dec_ref_known(v_varInfos_x3f_173_, 1);
v_sz_196_ = lean_array_size(v_val_195_);
v___x_197_ = ((size_t)0ULL);
v___x_198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(v_sz_196_, v___x_197_, v_val_195_);
v___y_177_ = v___x_198_;
goto v___jp_176_;
}
else
{
uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec(v_varInfos_x3f_173_);
v___x_199_ = 0;
v___x_200_ = lean_box(v___x_199_);
v___x_201_ = lean_mk_array(v_numArgs_175_, v___x_200_);
v___y_177_ = v___x_201_;
goto v___jp_176_;
}
v___jp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_auxVars_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_fvarIds_184_; size_t v_sz_185_; lean_object* v___x_186_; size_t v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v_fst_191_; lean_object* v_snd_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_mk_empty_array_with_capacity(v_numArgs_175_);
lean_inc_ref(v___x_179_);
v_auxVars_180_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_numArgs_175_, v___x_178_, v___x_179_);
v___x_181_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3);
v___x_182_ = lean_expr_instantiate_rev(v_pattern_174_, v_auxVars_180_);
lean_dec_ref(v_pattern_174_);
v___x_183_ = l_Lean_collectFVars(v___x_181_, v___x_182_);
v_fvarIds_184_ = lean_ctor_get(v___x_183_, 2);
lean_inc_ref(v_fvarIds_184_);
lean_dec_ref(v___x_183_);
v_sz_185_ = lean_array_size(v_fvarIds_184_);
v___x_186_ = ((lean_object*)(l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4));
v___x_187_ = ((size_t)0ULL);
v___x_188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(v_fvarIds_184_, v_sz_185_, v___x_187_, v___y_177_);
lean_dec_ref(v_fvarIds_184_);
v___x_189_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_180_, v_varTypes_172_, v_numArgs_175_, v___x_178_, v___x_179_);
lean_dec_ref(v_varTypes_172_);
v___x_190_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_numArgs_175_, v___x_188_, v_numArgs_175_, v_auxVars_180_, v___x_189_, v___x_178_, v___x_186_);
lean_dec_ref(v___x_189_);
lean_dec_ref(v_auxVars_180_);
lean_dec_ref(v___x_188_);
v_fst_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_fst_191_);
v_snd_192_ = lean_ctor_get(v___x_190_, 1);
lean_inc(v_snd_192_);
lean_dec_ref(v___x_190_);
v___x_193_ = l_Array_append___redArg(v_snd_192_, v_fst_191_);
lean_dec(v_fst_191_);
v___x_194_ = lean_array_to_list(v___x_193_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(lean_object* v_as_202_, lean_object* v_i_203_, lean_object* v_j_204_, lean_object* v_inv_205_, lean_object* v_bs_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_i_203_, v_j_204_, v_bs_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___boxed(lean_object* v_as_208_, lean_object* v_i_209_, lean_object* v_j_210_, lean_object* v_inv_211_, lean_object* v_bs_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(v_as_208_, v_i_209_, v_j_210_, v_inv_211_, v_bs_212_);
lean_dec_ref(v_as_208_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(lean_object* v_auxVars_214_, lean_object* v_as_215_, lean_object* v_i_216_, lean_object* v_j_217_, lean_object* v_inv_218_, lean_object* v_bs_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_214_, v_as_215_, v_i_216_, v_j_217_, v_bs_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___boxed(lean_object* v_auxVars_221_, lean_object* v_as_222_, lean_object* v_i_223_, lean_object* v_j_224_, lean_object* v_inv_225_, lean_object* v_bs_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(v_auxVars_221_, v_as_222_, v_i_223_, v_j_224_, v_inv_225_, v_bs_226_);
lean_dec_ref(v_as_222_);
lean_dec_ref(v_auxVars_221_);
return v_res_227_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(lean_object* v_upperBound_228_, lean_object* v___x_229_, lean_object* v___x_230_, lean_object* v___x_231_, lean_object* v_inst_232_, lean_object* v_R_233_, lean_object* v_a_234_, uint8_t v_b_235_, lean_object* v_c_236_){
_start:
{
uint8_t v___x_237_; 
v___x_237_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_upperBound_228_, v___x_229_, v___x_230_, v___x_231_, v_a_234_, v_b_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___boxed(lean_object* v_upperBound_238_, lean_object* v___x_239_, lean_object* v___x_240_, lean_object* v___x_241_, lean_object* v_inst_242_, lean_object* v_R_243_, lean_object* v_a_244_, lean_object* v_b_245_, lean_object* v_c_246_){
_start:
{
uint8_t v_b_boxed_247_; uint8_t v_res_248_; lean_object* v_r_249_; 
v_b_boxed_247_ = lean_unbox(v_b_245_);
v_res_248_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(v_upperBound_238_, v___x_239_, v___x_240_, v___x_241_, v_inst_242_, v_R_243_, v_a_244_, v_b_boxed_247_, v_c_246_);
lean_dec_ref(v___x_241_);
lean_dec_ref(v___x_240_);
lean_dec_ref(v___x_239_);
lean_dec(v_upperBound_238_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(lean_object* v_upperBound_250_, lean_object* v___x_251_, lean_object* v_numArgs_252_, lean_object* v_auxVars_253_, lean_object* v___x_254_, lean_object* v_inst_255_, lean_object* v_R_256_, lean_object* v_a_257_, lean_object* v_b_258_, lean_object* v_c_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_upperBound_250_, v___x_251_, v_numArgs_252_, v_auxVars_253_, v___x_254_, v_a_257_, v_b_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___boxed(lean_object* v_upperBound_261_, lean_object* v___x_262_, lean_object* v_numArgs_263_, lean_object* v_auxVars_264_, lean_object* v___x_265_, lean_object* v_inst_266_, lean_object* v_R_267_, lean_object* v_a_268_, lean_object* v_b_269_, lean_object* v_c_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(v_upperBound_261_, v___x_262_, v_numArgs_263_, v_auxVars_264_, v___x_265_, v_inst_266_, v_R_267_, v_a_268_, v_b_269_, v_c_270_);
lean_dec_ref(v___x_265_);
lean_dec_ref(v_auxVars_264_);
lean_dec(v_numArgs_263_);
lean_dec_ref(v___x_262_);
lean_dec(v_upperBound_261_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object* v_declName_272_, lean_object* v_num_x3f_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v___x_279_; 
lean_inc(v_declName_272_);
v___x_279_ = l_Lean_Meta_Sym_mkPatternFromDecl(v_declName_272_, v_num_x3f_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_291_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_291_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_291_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_291_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
lean_inc(v_a_280_);
v___x_284_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(v_a_280_);
v___x_285_ = lean_box(0);
v___x_286_ = l_Lean_mkConst(v_declName_272_, v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v_a_280_);
lean_ctor_set(v___x_287_, 2, v___x_284_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_287_);
v___x_289_ = v___x_282_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec(v_declName_272_);
v_a_292_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_279_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_279_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl___boxed(lean_object* v_declName_300_, lean_object* v_num_x3f_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v_declName_300_, v_num_x3f_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_num_x3f_301_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
if (lean_obj_tag(v_a_308_) == 0)
{
lean_object* v___x_310_; 
v___x_310_ = l_List_reverse___redArg(v_a_309_);
return v___x_310_;
}
else
{
lean_object* v_head_311_; lean_object* v_tail_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_321_; 
v_head_311_ = lean_ctor_get(v_a_308_, 0);
v_tail_312_ = lean_ctor_get(v_a_308_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_a_308_);
if (v_isSharedCheck_321_ == 0)
{
v___x_314_ = v_a_308_;
v_isShared_315_ = v_isSharedCheck_321_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_tail_312_);
lean_inc(v_head_311_);
lean_dec(v_a_308_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_321_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = l_Lean_mkLevelParam(v_head_311_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v_a_309_);
lean_ctor_set(v___x_314_, 0, v___x_316_);
v___x_318_ = v___x_314_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_a_309_);
v___x_318_ = v_reuseFailAlloc_320_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
v_a_308_ = v_tail_312_;
v_a_309_ = v___x_318_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object* v_e_322_, lean_object* v_levelParams_323_, lean_object* v_num_x3f_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_330_; 
lean_inc(v_levelParams_323_);
lean_inc_ref(v_e_322_);
v___x_330_ = l_Lean_Meta_Sym_mkPatternFromExpr(v_e_322_, v_levelParams_323_, v_num_x3f_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_344_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_344_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_344_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_344_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_levelParams_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v_levelParams_335_ = lean_ctor_get(v_a_331_, 0);
lean_inc(v_a_331_);
v___x_336_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(v_a_331_);
v___x_337_ = lean_box(0);
lean_inc(v_levelParams_335_);
v___x_338_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(v_levelParams_335_, v___x_337_);
v___x_339_ = l_Lean_Expr_instantiateLevelParams(v_e_322_, v_levelParams_323_, v___x_338_);
lean_dec_ref(v_e_322_);
v___x_340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_a_331_);
lean_ctor_set(v___x_340_, 2, v___x_336_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_340_);
v___x_342_ = v___x_333_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_levelParams_323_);
lean_dec_ref(v_e_322_);
v_a_345_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_330_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_330_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr___boxed(lean_object* v_e_353_, lean_object* v_levelParams_354_, lean_object* v_num_x3f_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_e_353_, v_levelParams_354_, v_num_x3f_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_num_x3f_355_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(lean_object* v_expr_362_, lean_object* v_pattern_363_, lean_object* v_result_364_){
_start:
{
if (lean_obj_tag(v_expr_362_) == 4)
{
lean_object* v_us_371_; 
v_us_371_ = lean_ctor_get(v_expr_362_, 1);
if (lean_obj_tag(v_us_371_) == 0)
{
lean_object* v_declName_372_; lean_object* v_us_373_; lean_object* v_args_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec_ref(v_pattern_363_);
v_declName_372_ = lean_ctor_get(v_expr_362_, 0);
lean_inc(v_declName_372_);
lean_dec_ref_known(v_expr_362_, 2);
v_us_373_ = lean_ctor_get(v_result_364_, 0);
lean_inc(v_us_373_);
v_args_374_ = lean_ctor_get(v_result_364_, 1);
lean_inc_ref(v_args_374_);
lean_dec_ref(v_result_364_);
v___x_375_ = l_Lean_mkConst(v_declName_372_, v_us_373_);
v___x_376_ = l_Lean_mkAppN(v___x_375_, v_args_374_);
lean_dec_ref(v_args_374_);
return v___x_376_;
}
else
{
goto v___jp_365_;
}
}
else
{
goto v___jp_365_;
}
v___jp_365_:
{
lean_object* v_levelParams_366_; lean_object* v_us_367_; lean_object* v_args_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_levelParams_366_ = lean_ctor_get(v_pattern_363_, 0);
lean_inc(v_levelParams_366_);
lean_dec_ref(v_pattern_363_);
v_us_367_ = lean_ctor_get(v_result_364_, 0);
lean_inc(v_us_367_);
v_args_368_ = lean_ctor_get(v_result_364_, 1);
lean_inc_ref(v_args_368_);
lean_dec_ref(v_result_364_);
v___x_369_ = l_Lean_Expr_instantiateLevelParams(v_expr_362_, v_levelParams_366_, v_us_367_);
lean_dec_ref(v_expr_362_);
v___x_370_ = l_Lean_mkAppN(v___x_369_, v_args_368_);
lean_dec_ref(v_args_368_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx(lean_object* v_x_377_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
lean_object* v___x_378_; 
v___x_378_ = lean_unsigned_to_nat(0u);
return v___x_378_;
}
else
{
lean_object* v___x_379_; 
v___x_379_ = lean_unsigned_to_nat(1u);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___boxed(lean_object* v_x_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Meta_Sym_ApplyResult_ctorIdx(v_x_380_);
lean_dec(v_x_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(lean_object* v_t_382_, lean_object* v_k_383_){
_start:
{
if (lean_obj_tag(v_t_382_) == 0)
{
return v_k_383_;
}
else
{
lean_object* v_mvarIds_384_; lean_object* v___x_385_; 
v_mvarIds_384_ = lean_ctor_get(v_t_382_, 0);
lean_inc(v_mvarIds_384_);
lean_dec_ref_known(v_t_382_, 1);
v___x_385_ = lean_apply_1(v_k_383_, v_mvarIds_384_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim(lean_object* v_motive_386_, lean_object* v_ctorIdx_387_, lean_object* v_t_388_, lean_object* v_h_389_, lean_object* v_k_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_388_, v_k_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___boxed(lean_object* v_motive_392_, lean_object* v_ctorIdx_393_, lean_object* v_t_394_, lean_object* v_h_395_, lean_object* v_k_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Meta_Sym_ApplyResult_ctorElim(v_motive_392_, v_ctorIdx_393_, v_t_394_, v_h_395_, v_k_396_);
lean_dec(v_ctorIdx_393_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim___redArg(lean_object* v_t_398_, lean_object* v_failed_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_398_, v_failed_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim(lean_object* v_motive_401_, lean_object* v_t_402_, lean_object* v_h_403_, lean_object* v_failed_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_402_, v_failed_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim___redArg(lean_object* v_t_406_, lean_object* v_goals_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_406_, v_goals_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim(lean_object* v_motive_409_, lean_object* v_t_410_, lean_object* v_h_411_, lean_object* v_goals_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_410_, v_goals_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(lean_object* v_x_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; 
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
v___x_422_ = lean_apply_7(v_x_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, lean_box(0));
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed(lean_object* v_x_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(v_x_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(lean_object* v_mvarId_432_, lean_object* v_x_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___f_441_; lean_object* v___x_442_; 
lean_inc(v___y_435_);
lean_inc_ref(v___y_434_);
v___f_441_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_441_, 0, v_x_433_);
lean_closure_set(v___f_441_, 1, v___y_434_);
lean_closure_set(v___f_441_, 2, v___y_435_);
v___x_442_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_432_, v___f_441_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_442_) == 0)
{
return v___x_442_;
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___boxed(lean_object* v_mvarId_451_, lean_object* v_x_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_451_, v_x_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(lean_object* v_00_u03b1_461_, lean_object* v_mvarId_462_, lean_object* v_x_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_462_, v_x_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___boxed(lean_object* v_00_u03b1_472_, lean_object* v_mvarId_473_, lean_object* v_x_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(v_00_u03b1_472_, v_mvarId_473_, v_x_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(lean_object* v_val_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
if (lean_obj_tag(v_a_484_) == 0)
{
lean_object* v___x_486_; 
v___x_486_ = l_List_reverse___redArg(v_a_485_);
return v___x_486_;
}
else
{
lean_object* v_head_487_; lean_object* v_tail_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_500_; 
v_head_487_ = lean_ctor_get(v_a_484_, 0);
v_tail_488_ = lean_ctor_get(v_a_484_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v_a_484_);
if (v_isSharedCheck_500_ == 0)
{
v___x_490_ = v_a_484_;
v_isShared_491_ = v_isSharedCheck_500_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_tail_488_);
lean_inc(v_head_487_);
lean_dec(v_a_484_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_500_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v_args_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
v_args_492_ = lean_ctor_get(v_val_483_, 1);
v___x_493_ = l_Lean_instInhabitedExpr;
v___x_494_ = lean_array_get_borrowed(v___x_493_, v_args_492_, v_head_487_);
lean_dec(v_head_487_);
v___x_495_ = l_Lean_Expr_mvarId_x21(v___x_494_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v_a_485_);
lean_ctor_set(v___x_490_, 0, v___x_495_);
v___x_497_ = v___x_490_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_a_485_);
v___x_497_ = v_reuseFailAlloc_499_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
v_a_484_ = v_tail_488_;
v_a_485_ = v___x_497_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1___boxed(lean_object* v_val_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(v_val_501_, v_a_502_, v_a_503_);
lean_dec_ref(v_val_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v_x_508_){
_start:
{
lean_object* v_ks_509_; lean_object* v_vs_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_534_; 
v_ks_509_ = lean_ctor_get(v_x_505_, 0);
v_vs_510_ = lean_ctor_get(v_x_505_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_534_ == 0)
{
v___x_512_ = v_x_505_;
v_isShared_513_ = v_isSharedCheck_534_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_vs_510_);
lean_inc(v_ks_509_);
lean_dec(v_x_505_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_534_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_array_get_size(v_ks_509_);
v___x_515_ = lean_nat_dec_lt(v_x_506_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
lean_dec(v_x_506_);
v___x_516_ = lean_array_push(v_ks_509_, v_x_507_);
v___x_517_ = lean_array_push(v_vs_510_, v_x_508_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v___x_517_);
lean_ctor_set(v___x_512_, 0, v___x_516_);
v___x_519_ = v___x_512_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
else
{
lean_object* v_k_x27_521_; uint8_t v___x_522_; 
v_k_x27_521_ = lean_array_fget_borrowed(v_ks_509_, v_x_506_);
v___x_522_ = l_Lean_instBEqMVarId_beq(v_x_507_, v_k_x27_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_524_; 
if (v_isShared_513_ == 0)
{
v___x_524_ = v___x_512_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_ks_509_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_vs_510_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_add(v_x_506_, v___x_525_);
lean_dec(v_x_506_);
v_x_505_ = v___x_524_;
v_x_506_ = v___x_526_;
goto _start;
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_529_ = lean_array_fset(v_ks_509_, v_x_506_, v_x_507_);
v___x_530_ = lean_array_fset(v_vs_510_, v_x_506_, v_x_508_);
lean_dec(v_x_506_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v___x_530_);
lean_ctor_set(v___x_512_, 0, v___x_529_);
v___x_532_ = v___x_512_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_535_, lean_object* v_k_536_, lean_object* v_v_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_535_, v___x_538_, v_k_536_, v_v_537_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(lean_object* v_x_541_, size_t v_x_542_, size_t v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
if (lean_obj_tag(v_x_541_) == 0)
{
lean_object* v_es_546_; size_t v___x_547_; size_t v___x_548_; lean_object* v_j_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_es_546_ = lean_ctor_get(v_x_541_, 0);
v___x_547_ = ((size_t)31ULL);
v___x_548_ = lean_usize_land(v_x_542_, v___x_547_);
v_j_549_ = lean_usize_to_nat(v___x_548_);
v___x_550_ = lean_array_get_size(v_es_546_);
v___x_551_ = lean_nat_dec_lt(v_j_549_, v___x_550_);
if (v___x_551_ == 0)
{
lean_dec(v_j_549_);
lean_dec(v_x_545_);
lean_dec(v_x_544_);
return v_x_541_;
}
else
{
lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_590_; 
lean_inc_ref(v_es_546_);
v_isSharedCheck_590_ = !lean_is_exclusive(v_x_541_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v_x_541_, 0);
lean_dec(v_unused_591_);
v___x_553_ = v_x_541_;
v_isShared_554_ = v_isSharedCheck_590_;
goto v_resetjp_552_;
}
else
{
lean_dec(v_x_541_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_590_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_v_555_; lean_object* v___x_556_; lean_object* v_xs_x27_557_; lean_object* v___y_559_; 
v_v_555_ = lean_array_fget(v_es_546_, v_j_549_);
v___x_556_ = lean_box(0);
v_xs_x27_557_ = lean_array_fset(v_es_546_, v_j_549_, v___x_556_);
switch(lean_obj_tag(v_v_555_))
{
case 0:
{
lean_object* v_key_564_; lean_object* v_val_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_575_; 
v_key_564_ = lean_ctor_get(v_v_555_, 0);
v_val_565_ = lean_ctor_get(v_v_555_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_v_555_);
if (v_isSharedCheck_575_ == 0)
{
v___x_567_ = v_v_555_;
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_val_565_);
lean_inc(v_key_564_);
lean_dec(v_v_555_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
uint8_t v___x_569_; 
v___x_569_ = l_Lean_instBEqMVarId_beq(v_x_544_, v_key_564_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_del_object(v___x_567_);
v___x_570_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_564_, v_val_565_, v_x_544_, v_x_545_);
v___x_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
v___y_559_ = v___x_571_;
goto v___jp_558_;
}
else
{
lean_object* v___x_573_; 
lean_dec(v_val_565_);
lean_dec(v_key_564_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v_x_545_);
lean_ctor_set(v___x_567_, 0, v_x_544_);
v___x_573_ = v___x_567_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_x_544_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_x_545_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
v___y_559_ = v___x_573_;
goto v___jp_558_;
}
}
}
}
case 1:
{
lean_object* v_node_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_588_; 
v_node_576_ = lean_ctor_get(v_v_555_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v_v_555_);
if (v_isSharedCheck_588_ == 0)
{
v___x_578_ = v_v_555_;
v_isShared_579_ = v_isSharedCheck_588_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_node_576_);
lean_dec(v_v_555_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_588_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
size_t v___x_580_; size_t v___x_581_; size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_580_ = ((size_t)5ULL);
v___x_581_ = lean_usize_shift_right(v_x_542_, v___x_580_);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_x_543_, v___x_582_);
v___x_584_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_node_576_, v___x_581_, v___x_583_, v_x_544_, v_x_545_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_584_);
v___x_586_ = v___x_578_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v___y_559_ = v___x_586_;
goto v___jp_558_;
}
}
}
default: 
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v_x_544_);
lean_ctor_set(v___x_589_, 1, v_x_545_);
v___y_559_ = v___x_589_;
goto v___jp_558_;
}
}
v___jp_558_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_array_fset(v_xs_x27_557_, v_j_549_, v___y_559_);
lean_dec(v_j_549_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_560_);
v___x_562_ = v___x_553_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
else
{
lean_object* v_ks_592_; lean_object* v_vs_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_613_; 
v_ks_592_ = lean_ctor_get(v_x_541_, 0);
v_vs_593_ = lean_ctor_get(v_x_541_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_x_541_);
if (v_isSharedCheck_613_ == 0)
{
v___x_595_ = v_x_541_;
v_isShared_596_ = v_isSharedCheck_613_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_vs_593_);
lean_inc(v_ks_592_);
lean_dec(v_x_541_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_613_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_ks_592_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_vs_593_);
v___x_598_ = v_reuseFailAlloc_612_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v_newNode_599_; uint8_t v___y_601_; size_t v___x_607_; uint8_t v___x_608_; 
v_newNode_599_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v___x_598_, v_x_544_, v_x_545_);
v___x_607_ = ((size_t)7ULL);
v___x_608_ = lean_usize_dec_le(v___x_607_, v_x_543_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_609_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_599_);
v___x_610_ = lean_unsigned_to_nat(4u);
v___x_611_ = lean_nat_dec_lt(v___x_609_, v___x_610_);
lean_dec(v___x_609_);
v___y_601_ = v___x_611_;
goto v___jp_600_;
}
else
{
v___y_601_ = v___x_608_;
goto v___jp_600_;
}
v___jp_600_:
{
if (v___y_601_ == 0)
{
lean_object* v_ks_602_; lean_object* v_vs_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_ks_602_ = lean_ctor_get(v_newNode_599_, 0);
lean_inc_ref(v_ks_602_);
v_vs_603_ = lean_ctor_get(v_newNode_599_, 1);
lean_inc_ref(v_vs_603_);
lean_dec_ref(v_newNode_599_);
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_606_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_x_543_, v_ks_602_, v_vs_603_, v___x_604_, v___x_605_);
lean_dec_ref(v_vs_603_);
lean_dec_ref(v_ks_602_);
return v___x_606_;
}
else
{
return v_newNode_599_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_614_, lean_object* v_keys_615_, lean_object* v_vals_616_, lean_object* v_i_617_, lean_object* v_entries_618_){
_start:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = lean_array_get_size(v_keys_615_);
v___x_620_ = lean_nat_dec_lt(v_i_617_, v___x_619_);
if (v___x_620_ == 0)
{
lean_dec(v_i_617_);
return v_entries_618_;
}
else
{
lean_object* v_k_621_; lean_object* v_v_622_; uint64_t v___x_623_; size_t v_h_624_; size_t v___x_625_; lean_object* v___x_626_; size_t v___x_627_; size_t v___x_628_; size_t v___x_629_; size_t v_h_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_k_621_ = lean_array_fget_borrowed(v_keys_615_, v_i_617_);
v_v_622_ = lean_array_fget_borrowed(v_vals_616_, v_i_617_);
v___x_623_ = l_Lean_instHashableMVarId_hash(v_k_621_);
v_h_624_ = lean_uint64_to_usize(v___x_623_);
v___x_625_ = ((size_t)5ULL);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = ((size_t)1ULL);
v___x_628_ = lean_usize_sub(v_depth_614_, v___x_627_);
v___x_629_ = lean_usize_mul(v___x_625_, v___x_628_);
v_h_630_ = lean_usize_shift_right(v_h_624_, v___x_629_);
v___x_631_ = lean_nat_add(v_i_617_, v___x_626_);
lean_dec(v_i_617_);
lean_inc(v_v_622_);
lean_inc(v_k_621_);
v___x_632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_entries_618_, v_h_630_, v_depth_614_, v_k_621_, v_v_622_);
v_i_617_ = v___x_631_;
v_entries_618_ = v___x_632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_634_, lean_object* v_keys_635_, lean_object* v_vals_636_, lean_object* v_i_637_, lean_object* v_entries_638_){
_start:
{
size_t v_depth_boxed_639_; lean_object* v_res_640_; 
v_depth_boxed_639_ = lean_unbox_usize(v_depth_634_);
lean_dec(v_depth_634_);
v_res_640_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_639_, v_keys_635_, v_vals_636_, v_i_637_, v_entries_638_);
lean_dec_ref(v_vals_636_);
lean_dec_ref(v_keys_635_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
size_t v_x_2811__boxed_646_; size_t v_x_2812__boxed_647_; lean_object* v_res_648_; 
v_x_2811__boxed_646_ = lean_unbox_usize(v_x_642_);
lean_dec(v_x_642_);
v_x_2812__boxed_647_ = lean_unbox_usize(v_x_643_);
lean_dec(v_x_643_);
v_res_648_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_641_, v_x_2811__boxed_646_, v_x_2812__boxed_647_, v_x_644_, v_x_645_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
uint64_t v___x_652_; size_t v___x_653_; size_t v___x_654_; lean_object* v___x_655_; 
v___x_652_ = l_Lean_instHashableMVarId_hash(v_x_650_);
v___x_653_ = lean_uint64_to_usize(v___x_652_);
v___x_654_ = ((size_t)1ULL);
v___x_655_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_649_, v___x_653_, v___x_654_, v_x_650_, v_x_651_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(lean_object* v_mvarId_656_, lean_object* v_val_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; lean_object* v_mctx_661_; lean_object* v_cache_662_; lean_object* v_zetaDeltaFVarIds_663_; lean_object* v_postponed_664_; lean_object* v_diag_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_693_; 
v___x_660_ = lean_st_ref_take(v___y_658_);
v_mctx_661_ = lean_ctor_get(v___x_660_, 0);
v_cache_662_ = lean_ctor_get(v___x_660_, 1);
v_zetaDeltaFVarIds_663_ = lean_ctor_get(v___x_660_, 2);
v_postponed_664_ = lean_ctor_get(v___x_660_, 3);
v_diag_665_ = lean_ctor_get(v___x_660_, 4);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_693_ == 0)
{
v___x_667_ = v___x_660_;
v_isShared_668_ = v_isSharedCheck_693_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_diag_665_);
lean_inc(v_postponed_664_);
lean_inc(v_zetaDeltaFVarIds_663_);
lean_inc(v_cache_662_);
lean_inc(v_mctx_661_);
lean_dec(v___x_660_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_693_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_depth_669_; lean_object* v_levelAssignDepth_670_; lean_object* v_lmvarCounter_671_; lean_object* v_mvarCounter_672_; lean_object* v_lDecls_673_; lean_object* v_decls_674_; lean_object* v_userNames_675_; lean_object* v_lAssignment_676_; lean_object* v_eAssignment_677_; lean_object* v_dAssignment_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_692_; 
v_depth_669_ = lean_ctor_get(v_mctx_661_, 0);
v_levelAssignDepth_670_ = lean_ctor_get(v_mctx_661_, 1);
v_lmvarCounter_671_ = lean_ctor_get(v_mctx_661_, 2);
v_mvarCounter_672_ = lean_ctor_get(v_mctx_661_, 3);
v_lDecls_673_ = lean_ctor_get(v_mctx_661_, 4);
v_decls_674_ = lean_ctor_get(v_mctx_661_, 5);
v_userNames_675_ = lean_ctor_get(v_mctx_661_, 6);
v_lAssignment_676_ = lean_ctor_get(v_mctx_661_, 7);
v_eAssignment_677_ = lean_ctor_get(v_mctx_661_, 8);
v_dAssignment_678_ = lean_ctor_get(v_mctx_661_, 9);
v_isSharedCheck_692_ = !lean_is_exclusive(v_mctx_661_);
if (v_isSharedCheck_692_ == 0)
{
v___x_680_ = v_mctx_661_;
v_isShared_681_ = v_isSharedCheck_692_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_dAssignment_678_);
lean_inc(v_eAssignment_677_);
lean_inc(v_lAssignment_676_);
lean_inc(v_userNames_675_);
lean_inc(v_decls_674_);
lean_inc(v_lDecls_673_);
lean_inc(v_mvarCounter_672_);
lean_inc(v_lmvarCounter_671_);
lean_inc(v_levelAssignDepth_670_);
lean_inc(v_depth_669_);
lean_dec(v_mctx_661_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_692_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_eAssignment_677_, v_mvarId_656_, v_val_657_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 8, v___x_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_depth_669_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_levelAssignDepth_670_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_lmvarCounter_671_);
lean_ctor_set(v_reuseFailAlloc_691_, 3, v_mvarCounter_672_);
lean_ctor_set(v_reuseFailAlloc_691_, 4, v_lDecls_673_);
lean_ctor_set(v_reuseFailAlloc_691_, 5, v_decls_674_);
lean_ctor_set(v_reuseFailAlloc_691_, 6, v_userNames_675_);
lean_ctor_set(v_reuseFailAlloc_691_, 7, v_lAssignment_676_);
lean_ctor_set(v_reuseFailAlloc_691_, 8, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_691_, 9, v_dAssignment_678_);
v___x_684_ = v_reuseFailAlloc_691_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_686_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_684_);
v___x_686_ = v___x_667_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_cache_662_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v_zetaDeltaFVarIds_663_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v_postponed_664_);
lean_ctor_set(v_reuseFailAlloc_690_, 4, v_diag_665_);
v___x_686_ = v_reuseFailAlloc_690_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_st_ref_set(v___y_658_, v___x_686_);
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg___boxed(lean_object* v_mvarId_694_, lean_object* v_val_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_694_, v_val_695_, v___y_696_);
lean_dec(v___y_696_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0(lean_object* v_mvarId_699_, lean_object* v_rule_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; 
lean_inc(v_mvarId_699_);
v___x_708_ = l_Lean_MVarId_getDecl(v_mvarId_699_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v_expr_710_; lean_object* v_pattern_711_; lean_object* v_resultPos_712_; lean_object* v_type_713_; uint8_t v___x_714_; lean_object* v___x_715_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v_expr_710_ = lean_ctor_get(v_rule_700_, 0);
lean_inc_ref(v_expr_710_);
v_pattern_711_ = lean_ctor_get(v_rule_700_, 1);
lean_inc_ref_n(v_pattern_711_, 2);
v_resultPos_712_ = lean_ctor_get(v_rule_700_, 2);
lean_inc(v_resultPos_712_);
lean_dec_ref(v_rule_700_);
v_type_713_ = lean_ctor_get(v_a_709_, 2);
lean_inc_ref(v_type_713_);
lean_dec(v_a_709_);
v___x_714_ = 1;
v___x_715_ = l_Lean_Meta_Sym_Pattern_unify_x3f(v_pattern_711_, v_type_713_, v___x_714_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_744_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_744_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_744_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_744_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
if (lean_obj_tag(v_a_716_) == 1)
{
lean_object* v_val_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_739_; 
lean_del_object(v___x_718_);
v_val_720_ = lean_ctor_get(v_a_716_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_a_716_);
if (v_isSharedCheck_739_ == 0)
{
v___x_722_ = v_a_716_;
v_isShared_723_ = v_isSharedCheck_739_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_val_720_);
lean_dec(v_a_716_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_739_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_737_; 
lean_inc(v_val_720_);
v___x_724_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(v_expr_710_, v_pattern_711_, v_val_720_);
v___x_725_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_699_, v___x_724_, v___y_704_);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v___x_725_, 0);
lean_dec(v_unused_738_);
v___x_727_ = v___x_725_;
v_isShared_728_ = v_isSharedCheck_737_;
goto v_resetjp_726_;
}
else
{
lean_dec(v___x_725_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_737_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_729_ = lean_box(0);
v___x_730_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(v_val_720_, v_resultPos_712_, v___x_729_);
lean_dec(v_val_720_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_730_);
v___x_732_ = v___x_722_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_736_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_734_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_732_);
v___x_734_ = v___x_727_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_742_; 
lean_dec(v_a_716_);
lean_dec(v_resultPos_712_);
lean_dec_ref(v_pattern_711_);
lean_dec_ref(v_expr_710_);
lean_dec(v_mvarId_699_);
v___x_740_ = lean_box(0);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_740_);
v___x_742_ = v___x_718_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v_resultPos_712_);
lean_dec_ref(v_pattern_711_);
lean_dec_ref(v_expr_710_);
lean_dec(v_mvarId_699_);
v_a_745_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_715_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_715_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
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
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v_rule_700_);
lean_dec(v_mvarId_699_);
v_a_753_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_708_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_708_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed(lean_object* v_mvarId_761_, lean_object* v_rule_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Meta_Sym_BackwardRule_apply___lam__0(v_mvarId_761_, v_rule_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object* v_mvarId_771_, lean_object* v_rule_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___f_780_; lean_object* v___x_781_; 
lean_inc(v_mvarId_771_);
v___f_780_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed), 9, 2);
lean_closure_set(v___f_780_, 0, v_mvarId_771_);
lean_closure_set(v___f_780_, 1, v_rule_772_);
v___x_781_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_771_, v___f_780_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___boxed(lean_object* v_mvarId_782_, lean_object* v_rule_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_782_, v_rule_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(lean_object* v_mvarId_792_, lean_object* v_val_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_792_, v_val_793_, v___y_797_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___boxed(lean_object* v_mvarId_802_, lean_object* v_val_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(v_mvarId_802_, v_val_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0(lean_object* v_00_u03b2_812_, lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_x_813_, v_x_814_, v_x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_817_, lean_object* v_x_818_, size_t v_x_819_, size_t v_x_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_818_, v_x_819_, v_x_820_, v_x_821_, v_x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_824_, lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v_x_829_){
_start:
{
size_t v_x_3184__boxed_830_; size_t v_x_3185__boxed_831_; lean_object* v_res_832_; 
v_x_3184__boxed_830_ = lean_unbox_usize(v_x_826_);
lean_dec(v_x_826_);
v_x_3185__boxed_831_ = lean_unbox_usize(v_x_827_);
lean_dec(v_x_827_);
v_res_832_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(v_00_u03b2_824_, v_x_825_, v_x_3184__boxed_830_, v_x_3185__boxed_831_, v_x_828_, v_x_829_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_833_, lean_object* v_n_834_, lean_object* v_k_835_, lean_object* v_v_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v_n_834_, v_k_835_, v_v_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_838_, size_t v_depth_839_, lean_object* v_keys_840_, lean_object* v_vals_841_, lean_object* v_heq_842_, lean_object* v_i_843_, lean_object* v_entries_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_839_, v_keys_840_, v_vals_841_, v_i_843_, v_entries_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_846_, lean_object* v_depth_847_, lean_object* v_keys_848_, lean_object* v_vals_849_, lean_object* v_heq_850_, lean_object* v_i_851_, lean_object* v_entries_852_){
_start:
{
size_t v_depth_boxed_853_; lean_object* v_res_854_; 
v_depth_boxed_853_ = lean_unbox_usize(v_depth_847_);
lean_dec(v_depth_847_);
v_res_854_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_846_, v_depth_boxed_853_, v_keys_848_, v_vals_849_, v_heq_850_, v_i_851_, v_entries_852_);
lean_dec_ref(v_vals_849_);
lean_dec_ref(v_keys_848_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_856_, v_x_857_, v_x_858_, v_x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(lean_object* v_msgData_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; lean_object* v_env_868_; lean_object* v___x_869_; lean_object* v_mctx_870_; lean_object* v_lctx_871_; lean_object* v_options_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_867_ = lean_st_ref_get(v___y_865_);
v_env_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc_ref(v_env_868_);
lean_dec(v___x_867_);
v___x_869_ = lean_st_ref_get(v___y_863_);
v_mctx_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc_ref(v_mctx_870_);
lean_dec(v___x_869_);
v_lctx_871_ = lean_ctor_get(v___y_862_, 2);
v_options_872_ = lean_ctor_get(v___y_864_, 2);
lean_inc_ref(v_options_872_);
lean_inc_ref(v_lctx_871_);
v___x_873_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_873_, 0, v_env_868_);
lean_ctor_set(v___x_873_, 1, v_mctx_870_);
lean_ctor_set(v___x_873_, 2, v_lctx_871_);
lean_ctor_set(v___x_873_, 3, v_options_872_);
v___x_874_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v_msgData_861_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0___boxed(lean_object* v_msgData_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msgData_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(lean_object* v_msg_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_ref_889_; lean_object* v___x_890_; lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_899_; 
v_ref_889_ = lean_ctor_get(v___y_886_, 5);
v___x_890_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msg_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_899_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_899_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_899_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
lean_inc(v_ref_889_);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v_ref_889_);
lean_ctor_set(v___x_895_, 1, v_a_891_);
if (v_isShared_894_ == 0)
{
lean_ctor_set_tag(v___x_893_, 1);
lean_ctor_set(v___x_893_, 0, v___x_895_);
v___x_897_ = v___x_893_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg___boxed(lean_object* v_msg_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v_msg_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_906_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0));
v___x_909_ = l_Lean_stringToMessageData(v___x_908_);
return v___x_909_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2));
v___x_912_ = l_Lean_stringToMessageData(v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27(lean_object* v_mvarId_913_, lean_object* v_rule_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___x_922_; 
lean_inc_ref(v_rule_914_);
lean_inc(v_mvarId_913_);
v___x_922_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_913_, v_rule_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_940_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_940_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_940_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_940_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
if (lean_obj_tag(v_a_923_) == 1)
{
lean_object* v_mvarIds_927_; lean_object* v___x_929_; 
lean_dec_ref(v_rule_914_);
lean_dec(v_mvarId_913_);
v_mvarIds_927_ = lean_ctor_get(v_a_923_, 0);
lean_inc(v_mvarIds_927_);
lean_dec_ref_known(v_a_923_, 1);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v_mvarIds_927_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_mvarIds_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
else
{
lean_object* v_expr_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_del_object(v___x_925_);
lean_dec(v_a_923_);
v_expr_931_ = lean_ctor_get(v_rule_914_, 0);
lean_inc_ref(v_expr_931_);
lean_dec_ref(v_rule_914_);
v___x_932_ = lean_obj_once(&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1, &l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1_once, _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1);
v___x_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_933_, 0, v_mvarId_913_);
v___x_934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_obj_once(&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3, &l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3_once, _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = l_Lean_indentExpr(v_expr_931_);
v___x_938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v___x_938_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
return v___x_939_;
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v_rule_914_);
lean_dec(v_mvarId_913_);
v_a_941_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_922_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_922_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___boxed(lean_object* v_mvarId_949_, lean_object* v_rule_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Meta_Sym_BackwardRule_apply_x27(v_mvarId_949_, v_rule_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(lean_object* v_00_u03b1_959_, lean_object* v_msg_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v_msg_960_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___boxed(lean_object* v_00_u03b1_969_, lean_object* v_msg_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(v_00_u03b1_969_, v_msg_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_978_;
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
