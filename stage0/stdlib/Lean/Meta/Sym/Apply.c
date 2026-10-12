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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_mkPatternFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___impl___boxed(lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(size_t v_sz_1_, size_t v_i_2_, lean_object* v_bs_3_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1_ = stack[0].m_num;
size_t v_i_2_ = stack[1].m_num;
lean_object* v_bs_3_ = stack[2].m_obj;
lean_object* v_res_14_;
v_res_14_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(v_sz_1_, v_i_2_, v_bs_3_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5___boxed(lean_object* v_sz_15_, lean_object* v_i_16_, lean_object* v_bs_17_){
_start:
{
size_t v_sz_boxed_18_; size_t v_i_boxed_19_; lean_object* v_res_20_; 
v_sz_boxed_18_ = lean_unbox_usize(v_sz_15_);
lean_dec(v_sz_15_);
v_i_boxed_19_ = lean_unbox_usize(v_i_16_);
lean_dec(v_i_16_);
v_res_20_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(v_sz_boxed_18_, v_i_boxed_19_, v_bs_17_);
return v_res_20_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(lean_object* v_as_24_, size_t v_sz_25_, size_t v_i_26_, lean_object* v_b_27_){
_start:
{
lean_object* v_a_29_; uint8_t v___x_33_; 
v___x_33_ = lean_usize_dec_lt(v_i_26_, v_sz_25_);
if (v___x_33_ == 0)
{
return v_b_27_;
}
else
{
lean_object* v_a_34_; 
v_a_34_ = lean_array_uget_borrowed(v_as_24_, v_i_26_);
if (lean_obj_tag(v_a_34_) == 2)
{
lean_object* v_pre_35_; lean_object* v_i_36_; lean_object* v_auxPrefix_37_; uint8_t v___x_38_; 
v_pre_35_ = lean_ctor_get(v_a_34_, 0);
v_i_36_ = lean_ctor_get(v_a_34_, 1);
v_auxPrefix_37_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1));
v___x_38_ = lean_name_eq(v_pre_35_, v_auxPrefix_37_);
if (v___x_38_ == 0)
{
v_a_29_ = v_b_27_;
goto v___jp_28_;
}
else
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_box(v___x_38_);
v___x_40_ = lean_array_set(v_b_27_, v_i_36_, v___x_39_);
v_a_29_ = v___x_40_;
goto v___jp_28_;
}
}
else
{
v_a_29_ = v_b_27_;
goto v___jp_28_;
}
}
v___jp_28_:
{
size_t v___x_30_; size_t v___x_31_; 
v___x_30_ = ((size_t)1ULL);
v___x_31_ = lean_usize_add(v_i_26_, v___x_30_);
v_i_26_ = v___x_31_;
v_b_27_ = v_a_29_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_24_ = stack[0].m_obj;
size_t v_sz_25_ = stack[1].m_num;
size_t v_i_26_ = stack[2].m_num;
lean_object* v_b_27_ = stack[3].m_obj;
lean_object* v_res_41_;
v_res_41_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(v_as_24_, v_sz_25_, v_i_26_, v_b_27_);
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___boxed(lean_object* v_as_42_, lean_object* v_sz_43_, lean_object* v_i_44_, lean_object* v_b_45_){
_start:
{
size_t v_sz_boxed_46_; size_t v_i_boxed_47_; lean_object* v_res_48_; 
v_sz_boxed_46_ = lean_unbox_usize(v_sz_43_);
lean_dec(v_sz_43_);
v_i_boxed_47_ = lean_unbox_usize(v_i_44_);
lean_dec(v_i_44_);
v_res_48_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(v_as_42_, v_sz_boxed_46_, v_i_boxed_47_, v_b_45_);
lean_dec_ref(v_as_42_);
return v_res_48_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(lean_object* v_auxVars_49_, size_t v_sz_50_, size_t v_i_51_, lean_object* v_bs_52_){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = lean_usize_dec_lt(v_i_51_, v_sz_50_);
if (v___x_53_ == 0)
{
return v_bs_52_;
}
else
{
lean_object* v_v_54_; lean_object* v___x_55_; lean_object* v_bs_x27_56_; lean_object* v___x_57_; lean_object* v___x_58_; size_t v___x_59_; size_t v___x_60_; lean_object* v___x_61_; 
v_v_54_ = lean_array_uget(v_bs_52_, v_i_51_);
v___x_55_ = lean_unsigned_to_nat(0u);
v_bs_x27_56_ = lean_array_uset(v_bs_52_, v_i_51_, v___x_55_);
v___x_57_ = lean_usize_to_nat(v_i_51_);
v___x_58_ = lean_expr_instantiate_rev_range(v_v_54_, v___x_55_, v___x_57_, v_auxVars_49_);
lean_dec(v___x_57_);
lean_dec(v_v_54_);
v___x_59_ = ((size_t)1ULL);
v___x_60_ = lean_usize_add(v_i_51_, v___x_59_);
v___x_61_ = lean_array_uset(v_bs_x27_56_, v_i_51_, v___x_58_);
v_i_51_ = v___x_60_;
v_bs_52_ = v___x_61_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxVars_49_ = stack[0].m_obj;
size_t v_sz_50_ = stack[1].m_num;
size_t v_i_51_ = stack[2].m_num;
lean_object* v_bs_52_ = stack[3].m_obj;
lean_object* v_res_63_;
v_res_63_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_49_, v_sz_50_, v_i_51_, v_bs_52_);
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg___boxed(lean_object* v_auxVars_64_, lean_object* v_sz_65_, lean_object* v_i_66_, lean_object* v_bs_67_){
_start:
{
size_t v_sz_boxed_68_; size_t v_i_boxed_69_; lean_object* v_res_70_; 
v_sz_boxed_68_ = lean_unbox_usize(v_sz_65_);
lean_dec(v_sz_65_);
v_i_boxed_69_ = lean_unbox_usize(v_i_66_);
lean_dec(v_i_66_);
v_res_70_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_64_, v_sz_boxed_68_, v_i_boxed_69_, v_bs_67_);
lean_dec_ref(v_auxVars_64_);
return v_res_70_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(lean_object* v_upperBound_71_, lean_object* v___x_72_, lean_object* v___x_73_, lean_object* v___x_74_, lean_object* v_next_75_, lean_object* v_upperBound_76_, lean_object* v_a_77_, uint8_t v_b_78_){
_start:
{
uint8_t v_a_80_; uint8_t v___x_84_; 
v___x_84_ = lean_nat_dec_lt(v_a_77_, v_upperBound_71_);
if (v___x_84_ == 0)
{
lean_dec(v_a_77_);
return v_b_78_;
}
else
{
uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_85_ = 0;
v___x_86_ = lean_box(v___x_85_);
v___x_87_ = lean_array_get(v___x_86_, v___x_72_, v_a_77_);
lean_dec(v___x_86_);
v___x_88_ = lean_unbox(v___x_87_);
lean_dec(v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_89_ = l_Lean_instInhabitedExpr;
v___x_90_ = lean_array_get_borrowed(v___x_89_, v___x_73_, v_a_77_);
v___x_91_ = l_Lean_Expr_fvarId_x21(v___x_74_);
v___x_92_ = l_Lean_Expr_containsFVar(v___x_90_, v___x_91_);
lean_dec(v___x_91_);
if (v___x_92_ == 0)
{
v_a_80_ = v_b_78_;
goto v___jp_79_;
}
else
{
uint8_t v___x_93_; 
lean_dec(v_a_77_);
v___x_93_ = lean_nat_dec_lt(v_next_75_, v_upperBound_76_);
return v___x_93_;
}
}
else
{
v_a_80_ = v_b_78_;
goto v___jp_79_;
}
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_add(v_a_77_, v___x_81_);
lean_dec(v_a_77_);
v_a_77_ = v___x_82_;
v_b_78_ = v_a_80_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_71_ = stack[0].m_obj;
lean_object* v___x_72_ = stack[1].m_obj;
lean_object* v___x_73_ = stack[2].m_obj;
lean_object* v___x_74_ = stack[3].m_obj;
lean_object* v_next_75_ = stack[4].m_obj;
lean_object* v_upperBound_76_ = stack[5].m_obj;
lean_object* v_a_77_ = stack[6].m_obj;
uint8_t v_b_78_ = stack[7].m_num;
uint8_t v_res_94_;
v_res_94_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_upperBound_71_, v___x_72_, v___x_73_, v___x_74_, v_next_75_, v_upperBound_76_, v_a_77_, v_b_78_);
stack->m_num = v_res_94_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg___boxed(lean_object* v_upperBound_95_, lean_object* v___x_96_, lean_object* v___x_97_, lean_object* v___x_98_, lean_object* v_next_99_, lean_object* v_upperBound_100_, lean_object* v_a_101_, lean_object* v_b_102_){
_start:
{
uint8_t v_b_boxed_103_; uint8_t v_res_104_; lean_object* v_r_105_; 
v_b_boxed_103_ = lean_unbox(v_b_102_);
v_res_104_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_upperBound_95_, v___x_96_, v___x_97_, v___x_98_, v_next_99_, v_upperBound_100_, v_a_101_, v_b_boxed_103_);
lean_dec(v_upperBound_100_);
lean_dec(v_next_99_);
lean_dec_ref(v___x_98_);
lean_dec_ref(v___x_97_);
lean_dec_ref(v___x_96_);
lean_dec(v_upperBound_95_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(lean_object* v_upperBound_106_, lean_object* v___x_107_, lean_object* v_numArgs_108_, lean_object* v_auxVars_109_, lean_object* v___x_110_, lean_object* v_a_111_, lean_object* v_b_112_){
_start:
{
lean_object* v_a_114_; uint8_t v___x_118_; 
v___x_118_ = lean_nat_dec_lt(v_a_111_, v_upperBound_106_);
if (v___x_118_ == 0)
{
lean_dec(v_a_111_);
return v_b_112_;
}
else
{
lean_object* v_fst_119_; lean_object* v_snd_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_145_; 
v_fst_119_ = lean_ctor_get(v_b_112_, 0);
v_snd_120_ = lean_ctor_get(v_b_112_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_b_112_);
if (v_isSharedCheck_145_ == 0)
{
v___x_122_ = v_b_112_;
v_isShared_123_ = v_isSharedCheck_145_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_snd_120_);
lean_inc(v_fst_119_);
lean_dec(v_b_112_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_145_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_124_ = 0;
v___x_125_ = lean_box(v___x_124_);
v___x_126_ = lean_array_get(v___x_125_, v___x_107_, v_a_111_);
lean_dec(v___x_125_);
v___x_127_ = lean_unbox(v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; uint8_t v___x_133_; 
v___x_128_ = l_Lean_instInhabitedExpr;
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_add(v_a_111_, v___x_129_);
v___x_131_ = lean_array_get_borrowed(v___x_128_, v_auxVars_109_, v_a_111_);
v___x_132_ = lean_unbox(v___x_126_);
lean_dec(v___x_126_);
v___x_133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_numArgs_108_, v___x_107_, v___x_110_, v___x_131_, v_a_111_, v_upperBound_106_, v___x_130_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_136_; 
lean_inc(v_a_111_);
v___x_134_ = lean_array_push(v_snd_120_, v_a_111_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_134_);
v___x_136_ = v___x_122_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_fst_119_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
v_a_114_ = v___x_136_;
goto v___jp_113_;
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_140_; 
lean_inc(v_a_111_);
v___x_138_ = lean_array_push(v_fst_119_, v_a_111_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_138_);
v___x_140_ = v___x_122_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_snd_120_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
v_a_114_ = v___x_140_;
goto v___jp_113_;
}
}
}
else
{
lean_object* v___x_143_; 
lean_dec(v___x_126_);
if (v_isShared_123_ == 0)
{
v___x_143_ = v___x_122_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_fst_119_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_snd_120_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
v_a_114_ = v___x_143_;
goto v___jp_113_;
}
}
}
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_add(v_a_111_, v___x_115_);
lean_dec(v_a_111_);
v_a_111_ = v___x_116_;
v_b_112_ = v_a_114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg___boxed(lean_object* v_upperBound_146_, lean_object* v___x_147_, lean_object* v_numArgs_148_, lean_object* v_auxVars_149_, lean_object* v___x_150_, lean_object* v_a_151_, lean_object* v_b_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_upperBound_146_, v___x_147_, v_numArgs_148_, v_auxVars_149_, v___x_150_, v_a_151_, v_b_152_);
lean_dec_ref(v___x_150_);
lean_dec_ref(v_auxVars_149_);
lean_dec(v_numArgs_148_);
lean_dec_ref(v___x_147_);
lean_dec(v_upperBound_146_);
return v_res_153_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(size_t v_sz_154_, size_t v_i_155_, lean_object* v_bs_156_){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = lean_usize_dec_lt(v_i_155_, v_sz_154_);
if (v___x_157_ == 0)
{
return v_bs_156_;
}
else
{
lean_object* v_auxPrefix_158_; lean_object* v___x_159_; lean_object* v_bs_x27_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; size_t v___x_164_; size_t v___x_165_; lean_object* v___x_166_; 
v_auxPrefix_158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1));
v___x_159_ = lean_unsigned_to_nat(0u);
v_bs_x27_160_ = lean_array_uset(v_bs_156_, v_i_155_, v___x_159_);
v___x_161_ = lean_usize_to_nat(v_i_155_);
v___x_162_ = l_Lean_Name_num___override(v_auxPrefix_158_, v___x_161_);
v___x_163_ = l_Lean_mkFVar(v___x_162_);
v___x_164_ = ((size_t)1ULL);
v___x_165_ = lean_usize_add(v_i_155_, v___x_164_);
v___x_166_ = lean_array_uset(v_bs_x27_160_, v_i_155_, v___x_163_);
v_i_155_ = v___x_165_;
v_bs_156_ = v___x_166_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_154_ = stack[0].m_num;
size_t v_i_155_ = stack[1].m_num;
lean_object* v_bs_156_ = stack[2].m_obj;
lean_object* v_res_168_;
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_sz_154_, v_i_155_, v_bs_156_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg___boxed(lean_object* v_sz_169_, lean_object* v_i_170_, lean_object* v_bs_171_){
_start:
{
size_t v_sz_boxed_172_; size_t v_i_boxed_173_; lean_object* v_res_174_; 
v_sz_boxed_172_ = lean_unbox_usize(v_sz_169_);
lean_dec(v_sz_169_);
v_i_boxed_173_ = lean_unbox_usize(v_i_170_);
lean_dec(v_i_170_);
v_res_174_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_sz_boxed_172_, v_i_boxed_173_, v_bs_171_);
return v_res_174_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_box(0);
v___x_176_ = lean_unsigned_to_nat(16u);
v___x_177_ = lean_mk_array(v___x_176_, v___x_175_);
return v___x_177_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0);
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_183_ = ((lean_object*)(l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2));
v___x_184_ = lean_box(1);
v___x_185_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1);
v___x_186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_184_);
lean_ctor_set(v___x_186_, 2, v___x_183_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(lean_object* v_pattern_189_){
_start:
{
lean_object* v_varTypes_190_; lean_object* v_varInfos_x3f_191_; lean_object* v_pattern_192_; lean_object* v_numArgs_193_; lean_object* v___y_195_; 
v_varTypes_190_ = lean_ctor_get(v_pattern_189_, 1);
lean_inc_ref(v_varTypes_190_);
v_varInfos_x3f_191_ = lean_ctor_get(v_pattern_189_, 2);
lean_inc(v_varInfos_x3f_191_);
v_pattern_192_ = lean_ctor_get(v_pattern_189_, 3);
lean_inc_ref(v_pattern_192_);
lean_dec_ref(v_pattern_189_);
v_numArgs_193_ = lean_array_get_size(v_varTypes_190_);
if (lean_obj_tag(v_varInfos_x3f_191_) == 1)
{
lean_object* v_val_213_; size_t v_sz_214_; size_t v___x_215_; lean_object* v___x_216_; 
v_val_213_ = lean_ctor_get(v_varInfos_x3f_191_, 0);
lean_inc(v_val_213_);
lean_dec_ref_known(v_varInfos_x3f_191_, 1);
v_sz_214_ = lean_array_size(v_val_213_);
v___x_215_ = ((size_t)0ULL);
v___x_216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(v_sz_214_, v___x_215_, v_val_213_);
v___y_195_ = v___x_216_;
goto v___jp_194_;
}
else
{
uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v_varInfos_x3f_191_);
v___x_217_ = 0;
v___x_218_ = lean_box(v___x_217_);
v___x_219_ = lean_mk_array(v_numArgs_193_, v___x_218_);
v___y_195_ = v___x_219_;
goto v___jp_194_;
}
v___jp_194_:
{
size_t v_sz_196_; size_t v___x_197_; lean_object* v_auxVars_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_fvarIds_203_; size_t v_sz_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_fst_209_; lean_object* v_snd_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_sz_196_ = lean_array_size(v_varTypes_190_);
v___x_197_ = ((size_t)0ULL);
lean_inc_ref(v_varTypes_190_);
v_auxVars_198_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_sz_196_, v___x_197_, v_varTypes_190_);
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_obj_once(&l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3, &l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3_once, _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3);
v___x_201_ = lean_expr_instantiate_rev(v_pattern_192_, v_auxVars_198_);
lean_dec_ref(v_pattern_192_);
v___x_202_ = l_Lean_collectFVars(v___x_200_, v___x_201_);
v_fvarIds_203_ = lean_ctor_get(v___x_202_, 2);
lean_inc_ref(v_fvarIds_203_);
lean_dec_ref(v___x_202_);
v_sz_204_ = lean_array_size(v_fvarIds_203_);
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4));
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(v_fvarIds_203_, v_sz_204_, v___x_197_, v___y_195_);
lean_dec_ref(v_fvarIds_203_);
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_198_, v_sz_196_, v___x_197_, v_varTypes_190_);
v___x_208_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_numArgs_193_, v___x_206_, v_numArgs_193_, v_auxVars_198_, v___x_207_, v___x_199_, v___x_205_);
lean_dec_ref(v___x_207_);
lean_dec_ref(v_auxVars_198_);
lean_dec_ref(v___x_206_);
v_fst_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_fst_209_);
v_snd_210_ = lean_ctor_get(v___x_208_, 1);
lean_inc(v_snd_210_);
lean_dec_ref(v___x_208_);
v___x_211_ = l_Array_append___redArg(v_snd_210_, v_fst_209_);
lean_dec(v_fst_209_);
v___x_212_ = lean_array_to_list(v___x_211_);
return v___x_212_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(lean_object* v_as_220_, size_t v_sz_221_, size_t v_i_222_, lean_object* v_bs_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_sz_221_, v_i_222_, v_bs_223_);
return v___x_224_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_220_ = stack[0].m_obj;
size_t v_sz_221_ = stack[1].m_num;
size_t v_i_222_ = stack[2].m_num;
lean_object* v_bs_223_ = stack[3].m_obj;
lean_object* v_res_225_;
v_res_225_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(v_as_220_, v_sz_221_, v_i_222_, v_bs_223_);
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___boxed(lean_object* v_as_226_, lean_object* v_sz_227_, lean_object* v_i_228_, lean_object* v_bs_229_){
_start:
{
size_t v_sz_boxed_230_; size_t v_i_boxed_231_; lean_object* v_res_232_; 
v_sz_boxed_230_ = lean_unbox_usize(v_sz_227_);
lean_dec(v_sz_227_);
v_i_boxed_231_ = lean_unbox_usize(v_i_228_);
lean_dec(v_i_228_);
v_res_232_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(v_as_226_, v_sz_boxed_230_, v_i_boxed_231_, v_bs_229_);
lean_dec_ref(v_as_226_);
return v_res_232_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(lean_object* v_auxVars_233_, lean_object* v_as_234_, size_t v_sz_235_, size_t v_i_236_, lean_object* v_bs_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_233_, v_sz_235_, v_i_236_, v_bs_237_);
return v___x_238_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxVars_233_ = stack[0].m_obj;
lean_object* v_as_234_ = stack[1].m_obj;
size_t v_sz_235_ = stack[2].m_num;
size_t v_i_236_ = stack[3].m_num;
lean_object* v_bs_237_ = stack[4].m_obj;
lean_object* v_res_239_;
v_res_239_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(v_auxVars_233_, v_as_234_, v_sz_235_, v_i_236_, v_bs_237_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___boxed(lean_object* v_auxVars_240_, lean_object* v_as_241_, lean_object* v_sz_242_, lean_object* v_i_243_, lean_object* v_bs_244_){
_start:
{
size_t v_sz_boxed_245_; size_t v_i_boxed_246_; lean_object* v_res_247_; 
v_sz_boxed_245_ = lean_unbox_usize(v_sz_242_);
lean_dec(v_sz_242_);
v_i_boxed_246_ = lean_unbox_usize(v_i_243_);
lean_dec(v_i_243_);
v_res_247_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(v_auxVars_240_, v_as_241_, v_sz_boxed_245_, v_i_boxed_246_, v_bs_244_);
lean_dec_ref(v_as_241_);
lean_dec_ref(v_auxVars_240_);
return v_res_247_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(lean_object* v_upperBound_248_, lean_object* v___x_249_, lean_object* v___x_250_, lean_object* v___x_251_, lean_object* v_next_252_, lean_object* v_upperBound_253_, lean_object* v_inst_254_, lean_object* v_R_255_, lean_object* v_a_256_, uint8_t v_b_257_, lean_object* v_c_258_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_upperBound_248_, v___x_249_, v___x_250_, v___x_251_, v_next_252_, v_upperBound_253_, v_a_256_, v_b_257_);
return v___x_259_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_248_ = stack[0].m_obj;
lean_object* v___x_249_ = stack[1].m_obj;
lean_object* v___x_250_ = stack[2].m_obj;
lean_object* v___x_251_ = stack[3].m_obj;
lean_object* v_next_252_ = stack[4].m_obj;
lean_object* v_upperBound_253_ = stack[5].m_obj;
lean_object* v_a_256_ = stack[8].m_obj;
uint8_t v_b_257_ = stack[9].m_num;
uint8_t v_res_260_;
v_res_260_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(v_upperBound_248_, v___x_249_, v___x_250_, v___x_251_, v_next_252_, v_upperBound_253_, lean_box(0), lean_box(0), v_a_256_, v_b_257_, lean_box(0));
stack->m_num = v_res_260_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___boxed(lean_object* v_upperBound_261_, lean_object* v___x_262_, lean_object* v___x_263_, lean_object* v___x_264_, lean_object* v_next_265_, lean_object* v_upperBound_266_, lean_object* v_inst_267_, lean_object* v_R_268_, lean_object* v_a_269_, lean_object* v_b_270_, lean_object* v_c_271_){
_start:
{
uint8_t v_b_boxed_272_; uint8_t v_res_273_; lean_object* v_r_274_; 
v_b_boxed_272_ = lean_unbox(v_b_270_);
v_res_273_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(v_upperBound_261_, v___x_262_, v___x_263_, v___x_264_, v_next_265_, v_upperBound_266_, v_inst_267_, v_R_268_, v_a_269_, v_b_boxed_272_, v_c_271_);
lean_dec(v_upperBound_266_);
lean_dec(v_next_265_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_262_);
lean_dec(v_upperBound_261_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(lean_object* v_upperBound_275_, lean_object* v___x_276_, lean_object* v_numArgs_277_, lean_object* v_auxVars_278_, lean_object* v___x_279_, lean_object* v_inst_280_, lean_object* v_R_281_, lean_object* v_a_282_, lean_object* v_b_283_, lean_object* v_c_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_upperBound_275_, v___x_276_, v_numArgs_277_, v_auxVars_278_, v___x_279_, v_a_282_, v_b_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___boxed(lean_object* v_upperBound_286_, lean_object* v___x_287_, lean_object* v_numArgs_288_, lean_object* v_auxVars_289_, lean_object* v___x_290_, lean_object* v_inst_291_, lean_object* v_R_292_, lean_object* v_a_293_, lean_object* v_b_294_, lean_object* v_c_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(v_upperBound_286_, v___x_287_, v_numArgs_288_, v_auxVars_289_, v___x_290_, v_inst_291_, v_R_292_, v_a_293_, v_b_294_, v_c_295_);
lean_dec_ref(v___x_290_);
lean_dec_ref(v_auxVars_289_);
lean_dec(v_numArgs_288_);
lean_dec_ref(v___x_287_);
lean_dec(v_upperBound_286_);
return v_res_296_;
}
}
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object* v_declName_297_, lean_object* v_num_x3f_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; 
lean_inc(v_declName_297_);
v___x_304_ = l_Lean_Meta_Sym_mkPatternFromDecl(v_declName_297_, v_num_x3f_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_316_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_316_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_316_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_316_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
lean_inc(v_a_305_);
v___x_309_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(v_a_305_);
v___x_310_ = lean_box(0);
v___x_311_ = l_Lean_mkConst(v_declName_297_, v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v_a_305_);
lean_ctor_set(v___x_312_, 2, v___x_309_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_312_);
v___x_314_ = v___x_307_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec(v_declName_297_);
v_a_317_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_304_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_304_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_mkBackwardRuleFromDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_297_ = stack[0].m_obj;
lean_object* v_num_x3f_298_ = stack[1].m_obj;
lean_object* v_a_299_ = stack[2].m_obj;
lean_object* v_a_300_ = stack[3].m_obj;
lean_object* v_a_301_ = stack[4].m_obj;
lean_object* v_a_302_ = stack[5].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v_declName_297_, v_num_x3f_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl___boxed(lean_object* v_declName_326_, lean_object* v_num_x3f_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v_declName_326_, v_num_x3f_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_num_x3f_327_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
if (lean_obj_tag(v_a_334_) == 0)
{
lean_object* v___x_336_; 
v___x_336_ = l_List_reverse___redArg(v_a_335_);
return v___x_336_;
}
else
{
lean_object* v_head_337_; lean_object* v_tail_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_347_; 
v_head_337_ = lean_ctor_get(v_a_334_, 0);
v_tail_338_ = lean_ctor_get(v_a_334_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_a_334_);
if (v_isSharedCheck_347_ == 0)
{
v___x_340_ = v_a_334_;
v_isShared_341_ = v_isSharedCheck_347_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_tail_338_);
lean_inc(v_head_337_);
lean_dec(v_a_334_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_347_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = l_Lean_mkLevelParam(v_head_337_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v_a_335_);
lean_ctor_set(v___x_340_, 0, v___x_342_);
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_a_335_);
v___x_344_ = v_reuseFailAlloc_346_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
v_a_334_ = v_tail_338_;
v_a_335_ = v___x_344_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr(lean_object* v_e_348_, lean_object* v_levelParams_349_, lean_object* v_num_x3f_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_356_; 
lean_inc(v_levelParams_349_);
lean_inc_ref(v_e_348_);
v___x_356_ = l_Lean_Meta_Sym_mkPatternFromExpr(v_e_348_, v_levelParams_349_, v_num_x3f_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_370_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_370_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_370_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_370_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_levelParams_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v_levelParams_361_ = lean_ctor_get(v_a_357_, 0);
lean_inc(v_a_357_);
v___x_362_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(v_a_357_);
v___x_363_ = lean_box(0);
lean_inc(v_levelParams_361_);
v___x_364_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(v_levelParams_361_, v___x_363_);
v___x_365_ = l_Lean_Expr_instantiateLevelParams(v_e_348_, v_levelParams_349_, v___x_364_);
lean_dec_ref(v_e_348_);
v___x_366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_a_357_);
lean_ctor_set(v___x_366_, 2, v___x_362_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_366_);
v___x_368_ = v___x_359_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v_levelParams_349_);
lean_dec_ref(v_e_348_);
v_a_371_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_356_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_356_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_mkBackwardRuleFromExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_348_ = stack[0].m_obj;
lean_object* v_levelParams_349_ = stack[1].m_obj;
lean_object* v_num_x3f_350_ = stack[2].m_obj;
lean_object* v_a_351_ = stack[3].m_obj;
lean_object* v_a_352_ = stack[4].m_obj;
lean_object* v_a_353_ = stack[5].m_obj;
lean_object* v_a_354_ = stack[6].m_obj;
lean_object* v_res_379_;
v_res_379_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_e_348_, v_levelParams_349_, v_num_x3f_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
stack->m_obj
 = v_res_379_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromExpr___boxed(lean_object* v_e_380_, lean_object* v_levelParams_381_, lean_object* v_num_x3f_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(v_e_380_, v_levelParams_381_, v_num_x3f_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_num_x3f_382_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(lean_object* v_expr_389_, lean_object* v_pattern_390_, lean_object* v_result_391_){
_start:
{
if (lean_obj_tag(v_expr_389_) == 4)
{
lean_object* v_us_398_; 
v_us_398_ = lean_ctor_get(v_expr_389_, 1);
if (lean_obj_tag(v_us_398_) == 0)
{
lean_object* v_declName_399_; lean_object* v_us_400_; lean_object* v_args_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec_ref(v_pattern_390_);
v_declName_399_ = lean_ctor_get(v_expr_389_, 0);
lean_inc(v_declName_399_);
lean_dec_ref_known(v_expr_389_, 2);
v_us_400_ = lean_ctor_get(v_result_391_, 0);
lean_inc(v_us_400_);
v_args_401_ = lean_ctor_get(v_result_391_, 1);
lean_inc_ref(v_args_401_);
lean_dec_ref(v_result_391_);
v___x_402_ = l_Lean_mkConst(v_declName_399_, v_us_400_);
v___x_403_ = l_Lean_mkAppN(v___x_402_, v_args_401_);
lean_dec_ref(v_args_401_);
return v___x_403_;
}
else
{
goto v___jp_392_;
}
}
else
{
goto v___jp_392_;
}
v___jp_392_:
{
lean_object* v_levelParams_393_; lean_object* v_us_394_; lean_object* v_args_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_levelParams_393_ = lean_ctor_get(v_pattern_390_, 0);
lean_inc(v_levelParams_393_);
lean_dec_ref(v_pattern_390_);
v_us_394_ = lean_ctor_get(v_result_391_, 0);
lean_inc(v_us_394_);
v_args_395_ = lean_ctor_get(v_result_391_, 1);
lean_inc_ref(v_args_395_);
lean_dec_ref(v_result_391_);
v___x_396_ = l_Lean_Expr_instantiateLevelParams(v_expr_389_, v_levelParams_393_, v_us_394_);
lean_dec_ref(v_expr_389_);
v___x_397_ = l_Lean_mkAppN(v___x_396_, v_args_395_);
lean_dec_ref(v_args_395_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___impl(lean_object* v_x_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = lean_obj_tag_nat(v_x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorIdx___impl___boxed(lean_object* v_x_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Meta_Sym_ApplyResult_ctorIdx___impl(v_x_406_);
lean_dec(v_x_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(lean_object* v_t_408_, lean_object* v_k_409_){
_start:
{
if (lean_obj_tag(v_t_408_) == 0)
{
return v_k_409_;
}
else
{
lean_object* v_mvarIds_410_; lean_object* v___x_411_; 
v_mvarIds_410_ = lean_ctor_get(v_t_408_, 0);
lean_inc(v_mvarIds_410_);
lean_dec_ref_known(v_t_408_, 1);
v___x_411_ = lean_apply_1(v_k_409_, v_mvarIds_410_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim(lean_object* v_motive_412_, lean_object* v_ctorIdx_413_, lean_object* v_t_414_, lean_object* v_h_415_, lean_object* v_k_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_414_, v_k_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_ctorElim___boxed(lean_object* v_motive_418_, lean_object* v_ctorIdx_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_k_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Meta_Sym_ApplyResult_ctorElim(v_motive_418_, v_ctorIdx_419_, v_t_420_, v_h_421_, v_k_422_);
lean_dec(v_ctorIdx_419_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim___redArg(lean_object* v_t_424_, lean_object* v_failed_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_424_, v_failed_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_failed_elim(lean_object* v_motive_427_, lean_object* v_t_428_, lean_object* v_h_429_, lean_object* v_failed_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_428_, v_failed_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim___redArg(lean_object* v_t_432_, lean_object* v_goals_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_432_, v_goals_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_ApplyResult_goals_elim(lean_object* v_motive_435_, lean_object* v_t_436_, lean_object* v_h_437_, lean_object* v_goals_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_436_, v_goals_438_);
return v___x_439_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(lean_object* v_x_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; 
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
v___x_448_ = lean_apply_7(v_x_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, lean_box(0));
return v___x_448_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_440_ = stack[0].m_obj;
lean_object* v___y_441_ = stack[1].m_obj;
lean_object* v___y_442_ = stack[2].m_obj;
lean_object* v___y_443_ = stack[3].m_obj;
lean_object* v___y_444_ = stack[4].m_obj;
lean_object* v___y_445_ = stack[5].m_obj;
lean_object* v___y_446_ = stack[6].m_obj;
lean_object* v_res_449_;
v_res_449_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(v_x_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed(lean_object* v_x_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(v_x_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_458_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(lean_object* v_mvarId_459_, lean_object* v_x_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___f_468_; lean_object* v___x_469_; 
lean_inc(v___y_462_);
lean_inc_ref(v___y_461_);
v___f_468_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_468_, 0, v_x_460_);
lean_closure_set(v___f_468_, 1, v___y_461_);
lean_closure_set(v___f_468_, 2, v___y_462_);
v___x_469_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_459_, v___f_468_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_469_) == 0)
{
return v___x_469_;
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_459_ = stack[0].m_obj;
lean_object* v_x_460_ = stack[1].m_obj;
lean_object* v___y_461_ = stack[2].m_obj;
lean_object* v___y_462_ = stack[3].m_obj;
lean_object* v___y_463_ = stack[4].m_obj;
lean_object* v___y_464_ = stack[5].m_obj;
lean_object* v___y_465_ = stack[6].m_obj;
lean_object* v___y_466_ = stack[7].m_obj;
lean_object* v_res_478_;
v_res_478_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_459_, v_x_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___boxed(lean_object* v_mvarId_479_, lean_object* v_x_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_479_, v_x_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v_res_488_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(lean_object* v_00_u03b1_489_, lean_object* v_mvarId_490_, lean_object* v_x_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_490_, v_x_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
return v___x_499_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_490_ = stack[1].m_obj;
lean_object* v_x_491_ = stack[2].m_obj;
lean_object* v___y_492_ = stack[3].m_obj;
lean_object* v___y_493_ = stack[4].m_obj;
lean_object* v___y_494_ = stack[5].m_obj;
lean_object* v___y_495_ = stack[6].m_obj;
lean_object* v___y_496_ = stack[7].m_obj;
lean_object* v___y_497_ = stack[8].m_obj;
lean_object* v_res_500_;
v_res_500_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(lean_box(0), v_mvarId_490_, v_x_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
stack->m_obj
 = v_res_500_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___boxed(lean_object* v_00_u03b1_501_, lean_object* v_mvarId_502_, lean_object* v_x_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(v_00_u03b1_501_, v_mvarId_502_, v_x_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(lean_object* v_val_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
if (lean_obj_tag(v_a_513_) == 0)
{
lean_object* v___x_515_; 
v___x_515_ = l_List_reverse___redArg(v_a_514_);
return v___x_515_;
}
else
{
lean_object* v_head_516_; lean_object* v_tail_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_529_; 
v_head_516_ = lean_ctor_get(v_a_513_, 0);
v_tail_517_ = lean_ctor_get(v_a_513_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_a_513_);
if (v_isSharedCheck_529_ == 0)
{
v___x_519_ = v_a_513_;
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_tail_517_);
lean_inc(v_head_516_);
lean_dec(v_a_513_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_args_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v_args_521_ = lean_ctor_get(v_val_512_, 1);
v___x_522_ = l_Lean_instInhabitedExpr;
v___x_523_ = lean_array_get_borrowed(v___x_522_, v_args_521_, v_head_516_);
lean_dec(v_head_516_);
v___x_524_ = l_Lean_Expr_mvarId_x21(v___x_523_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v_a_514_);
lean_ctor_set(v___x_519_, 0, v___x_524_);
v___x_526_ = v___x_519_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_a_514_);
v___x_526_ = v_reuseFailAlloc_528_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v_a_513_ = v_tail_517_;
v_a_514_ = v___x_526_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1___boxed(lean_object* v_val_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(v_val_530_, v_a_531_, v_a_532_);
lean_dec_ref(v_val_530_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
lean_object* v_ks_538_; lean_object* v_vs_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_563_; 
v_ks_538_ = lean_ctor_get(v_x_534_, 0);
v_vs_539_ = lean_ctor_get(v_x_534_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_x_534_);
if (v_isSharedCheck_563_ == 0)
{
v___x_541_ = v_x_534_;
v_isShared_542_ = v_isSharedCheck_563_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_vs_539_);
lean_inc(v_ks_538_);
lean_dec(v_x_534_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_563_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_array_get_size(v_ks_538_);
v___x_544_ = lean_nat_dec_lt(v_x_535_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
lean_dec(v_x_535_);
v___x_545_ = lean_array_push(v_ks_538_, v_x_536_);
v___x_546_ = lean_array_push(v_vs_539_, v_x_537_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_546_);
lean_ctor_set(v___x_541_, 0, v___x_545_);
v___x_548_ = v___x_541_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
else
{
lean_object* v_k_x27_550_; uint8_t v___x_551_; 
v_k_x27_550_ = lean_array_fget_borrowed(v_ks_538_, v_x_535_);
v___x_551_ = l_Lean_instBEqMVarId_beq(v_x_536_, v_k_x27_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_553_; 
if (v_isShared_542_ == 0)
{
v___x_553_ = v___x_541_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_ks_538_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_vs_539_);
v___x_553_ = v_reuseFailAlloc_557_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_nat_add(v_x_535_, v___x_554_);
lean_dec(v_x_535_);
v_x_534_ = v___x_553_;
v_x_535_ = v___x_555_;
goto _start;
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_558_ = lean_array_fset(v_ks_538_, v_x_535_, v_x_536_);
v___x_559_ = lean_array_fset(v_vs_539_, v_x_535_, v_x_537_);
lean_dec(v_x_535_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_559_);
lean_ctor_set(v___x_541_, 0, v___x_558_);
v___x_561_ = v___x_541_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_564_, lean_object* v_k_565_, lean_object* v_v_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_564_, v___x_567_, v_k_565_, v_v_566_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_569_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(lean_object* v_x_570_, size_t v_x_571_, size_t v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
if (lean_obj_tag(v_x_570_) == 0)
{
lean_object* v_es_575_; size_t v___x_576_; size_t v___x_577_; lean_object* v_j_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_es_575_ = lean_ctor_get(v_x_570_, 0);
v___x_576_ = ((size_t)31ULL);
v___x_577_ = lean_usize_land(v_x_571_, v___x_576_);
v_j_578_ = lean_usize_to_nat(v___x_577_);
v___x_579_ = lean_array_get_size(v_es_575_);
v___x_580_ = lean_nat_dec_lt(v_j_578_, v___x_579_);
if (v___x_580_ == 0)
{
lean_dec(v_j_578_);
lean_dec(v_x_574_);
lean_dec(v_x_573_);
return v_x_570_;
}
else
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_619_; 
lean_inc_ref(v_es_575_);
v_isSharedCheck_619_ = !lean_is_exclusive(v_x_570_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v_x_570_, 0);
lean_dec(v_unused_620_);
v___x_582_ = v_x_570_;
v_isShared_583_ = v_isSharedCheck_619_;
goto v_resetjp_581_;
}
else
{
lean_dec(v_x_570_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_619_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_v_584_; lean_object* v___x_585_; lean_object* v_xs_x27_586_; lean_object* v___y_588_; 
v_v_584_ = lean_array_fget(v_es_575_, v_j_578_);
v___x_585_ = lean_box(0);
v_xs_x27_586_ = lean_array_fset(v_es_575_, v_j_578_, v___x_585_);
switch(lean_obj_tag(v_v_584_))
{
case 0:
{
lean_object* v_key_593_; lean_object* v_val_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_604_; 
v_key_593_ = lean_ctor_get(v_v_584_, 0);
v_val_594_ = lean_ctor_get(v_v_584_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_v_584_);
if (v_isSharedCheck_604_ == 0)
{
v___x_596_ = v_v_584_;
v_isShared_597_ = v_isSharedCheck_604_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_val_594_);
lean_inc(v_key_593_);
lean_dec(v_v_584_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_604_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
uint8_t v___x_598_; 
v___x_598_ = l_Lean_instBEqMVarId_beq(v_x_573_, v_key_593_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_del_object(v___x_596_);
v___x_599_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_593_, v_val_594_, v_x_573_, v_x_574_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
v___y_588_ = v___x_600_;
goto v___jp_587_;
}
else
{
lean_object* v___x_602_; 
lean_dec(v_val_594_);
lean_dec(v_key_593_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v_x_574_);
lean_ctor_set(v___x_596_, 0, v_x_573_);
v___x_602_ = v___x_596_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_x_573_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_x_574_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
v___y_588_ = v___x_602_;
goto v___jp_587_;
}
}
}
}
case 1:
{
lean_object* v_node_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_617_; 
v_node_605_ = lean_ctor_get(v_v_584_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v_v_584_);
if (v_isSharedCheck_617_ == 0)
{
v___x_607_ = v_v_584_;
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_node_605_);
lean_dec(v_v_584_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_609_ = ((size_t)5ULL);
v___x_610_ = lean_usize_shift_right(v_x_571_, v___x_609_);
v___x_611_ = ((size_t)1ULL);
v___x_612_ = lean_usize_add(v_x_572_, v___x_611_);
v___x_613_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_node_605_, v___x_610_, v___x_612_, v_x_573_, v_x_574_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_613_);
v___x_615_ = v___x_607_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
v___y_588_ = v___x_615_;
goto v___jp_587_;
}
}
}
default: 
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v_x_573_);
lean_ctor_set(v___x_618_, 1, v_x_574_);
v___y_588_ = v___x_618_;
goto v___jp_587_;
}
}
v___jp_587_:
{
lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_589_ = lean_array_fset(v_xs_x27_586_, v_j_578_, v___y_588_);
lean_dec(v_j_578_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_589_);
v___x_591_ = v___x_582_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
else
{
lean_object* v_ks_621_; lean_object* v_vs_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_640_; 
v_ks_621_ = lean_ctor_get(v_x_570_, 0);
v_vs_622_ = lean_ctor_get(v_x_570_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_570_);
if (v_isSharedCheck_640_ == 0)
{
v___x_624_ = v_x_570_;
v_isShared_625_ = v_isSharedCheck_640_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_vs_622_);
lean_inc(v_ks_621_);
lean_dec(v_x_570_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_640_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_ks_621_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_vs_622_);
v___x_627_ = v_reuseFailAlloc_639_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v_newNode_628_; size_t v___x_629_; uint8_t v___x_630_; 
v_newNode_628_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v___x_627_, v_x_573_, v_x_574_);
v___x_629_ = ((size_t)7ULL);
v___x_630_ = lean_usize_dec_le(v___x_629_, v_x_572_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_631_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_628_);
v___x_632_ = lean_unsigned_to_nat(4u);
v___x_633_ = lean_nat_dec_lt(v___x_631_, v___x_632_);
lean_dec(v___x_631_);
if (v___x_633_ == 0)
{
lean_object* v_ks_634_; lean_object* v_vs_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_ks_634_ = lean_ctor_get(v_newNode_628_, 0);
lean_inc_ref(v_ks_634_);
v_vs_635_ = lean_ctor_get(v_newNode_628_, 1);
lean_inc_ref(v_vs_635_);
lean_dec_ref(v_newNode_628_);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_638_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_x_572_, v_ks_634_, v_vs_635_, v___x_636_, v___x_637_);
lean_dec_ref(v_vs_635_);
lean_dec_ref(v_ks_634_);
return v___x_638_;
}
else
{
return v_newNode_628_;
}
}
else
{
return v_newNode_628_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_570_ = stack[0].m_obj;
size_t v_x_571_ = stack[1].m_num;
size_t v_x_572_ = stack[2].m_num;
lean_object* v_x_573_ = stack[3].m_obj;
lean_object* v_x_574_ = stack[4].m_obj;
lean_object* v_res_641_;
v_res_641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_570_, v_x_571_, v_x_572_, v_x_573_, v_x_574_);
stack->m_obj
 = v_res_641_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_642_, lean_object* v_keys_643_, lean_object* v_vals_644_, lean_object* v_i_645_, lean_object* v_entries_646_){
_start:
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_array_get_size(v_keys_643_);
v___x_648_ = lean_nat_dec_lt(v_i_645_, v___x_647_);
if (v___x_648_ == 0)
{
lean_dec(v_i_645_);
return v_entries_646_;
}
else
{
lean_object* v_k_649_; lean_object* v_v_650_; uint64_t v___x_651_; size_t v_h_652_; size_t v___x_653_; lean_object* v___x_654_; size_t v___x_655_; size_t v___x_656_; size_t v___x_657_; size_t v_h_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_k_649_ = lean_array_fget_borrowed(v_keys_643_, v_i_645_);
v_v_650_ = lean_array_fget_borrowed(v_vals_644_, v_i_645_);
v___x_651_ = l_Lean_instHashableMVarId_hash(v_k_649_);
v_h_652_ = lean_uint64_to_usize(v___x_651_);
v___x_653_ = ((size_t)5ULL);
v___x_654_ = lean_unsigned_to_nat(1u);
v___x_655_ = ((size_t)1ULL);
v___x_656_ = lean_usize_sub(v_depth_642_, v___x_655_);
v___x_657_ = lean_usize_mul(v___x_653_, v___x_656_);
v_h_658_ = lean_usize_shift_right(v_h_652_, v___x_657_);
v___x_659_ = lean_nat_add(v_i_645_, v___x_654_);
lean_dec(v_i_645_);
lean_inc(v_v_650_);
lean_inc(v_k_649_);
v___x_660_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_entries_646_, v_h_658_, v_depth_642_, v_k_649_, v_v_650_);
v_i_645_ = v___x_659_;
v_entries_646_ = v___x_660_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_642_ = stack[0].m_num;
lean_object* v_keys_643_ = stack[1].m_obj;
lean_object* v_vals_644_ = stack[2].m_obj;
lean_object* v_i_645_ = stack[3].m_obj;
lean_object* v_entries_646_ = stack[4].m_obj;
lean_object* v_res_662_;
v_res_662_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_642_, v_keys_643_, v_vals_644_, v_i_645_, v_entries_646_);
stack->m_obj
 = v_res_662_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_663_, lean_object* v_keys_664_, lean_object* v_vals_665_, lean_object* v_i_666_, lean_object* v_entries_667_){
_start:
{
size_t v_depth_boxed_668_; lean_object* v_res_669_; 
v_depth_boxed_668_ = lean_unbox_usize(v_depth_663_);
lean_dec(v_depth_663_);
v_res_669_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_668_, v_keys_664_, v_vals_665_, v_i_666_, v_entries_667_);
lean_dec_ref(v_vals_665_);
lean_dec_ref(v_keys_664_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
size_t v_x_3135__boxed_675_; size_t v_x_3136__boxed_676_; lean_object* v_res_677_; 
v_x_3135__boxed_675_ = lean_unbox_usize(v_x_671_);
lean_dec(v_x_671_);
v_x_3136__boxed_676_ = lean_unbox_usize(v_x_672_);
lean_dec(v_x_672_);
v_res_677_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_670_, v_x_3135__boxed_675_, v_x_3136__boxed_676_, v_x_673_, v_x_674_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
uint64_t v___x_681_; size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___x_681_ = l_Lean_instHashableMVarId_hash(v_x_679_);
v___x_682_ = lean_uint64_to_usize(v___x_681_);
v___x_683_ = ((size_t)1ULL);
v___x_684_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_678_, v___x_682_, v___x_683_, v_x_679_, v_x_680_);
return v___x_684_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(lean_object* v_mvarId_685_, lean_object* v_val_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; lean_object* v_mctx_690_; lean_object* v_cache_691_; lean_object* v_zetaDeltaFVarIds_692_; lean_object* v_postponed_693_; lean_object* v_diag_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_724_; 
v___x_689_ = lean_st_ref_take(v___y_687_);
v_mctx_690_ = lean_ctor_get(v___x_689_, 0);
v_cache_691_ = lean_ctor_get(v___x_689_, 1);
v_zetaDeltaFVarIds_692_ = lean_ctor_get(v___x_689_, 2);
v_postponed_693_ = lean_ctor_get(v___x_689_, 3);
v_diag_694_ = lean_ctor_get(v___x_689_, 4);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_724_ == 0)
{
v___x_696_ = v___x_689_;
v_isShared_697_ = v_isSharedCheck_724_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_diag_694_);
lean_inc(v_postponed_693_);
lean_inc(v_zetaDeltaFVarIds_692_);
lean_inc(v_cache_691_);
lean_inc(v_mctx_690_);
lean_dec(v___x_689_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_724_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v_depth_698_; lean_object* v_levelAssignDepth_699_; lean_object* v_lmvarCounter_700_; lean_object* v_mvarCounter_701_; lean_object* v_lDecls_702_; lean_object* v_decls_703_; lean_object* v_userNames_704_; lean_object* v_lAssignment_705_; lean_object* v_eAssignment_706_; lean_object* v_dAssignment_707_; lean_object* v_instanceTypedMVars_708_; lean_object* v_synthNormMemo_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_723_; 
v_depth_698_ = lean_ctor_get(v_mctx_690_, 0);
v_levelAssignDepth_699_ = lean_ctor_get(v_mctx_690_, 1);
v_lmvarCounter_700_ = lean_ctor_get(v_mctx_690_, 2);
v_mvarCounter_701_ = lean_ctor_get(v_mctx_690_, 3);
v_lDecls_702_ = lean_ctor_get(v_mctx_690_, 4);
v_decls_703_ = lean_ctor_get(v_mctx_690_, 5);
v_userNames_704_ = lean_ctor_get(v_mctx_690_, 6);
v_lAssignment_705_ = lean_ctor_get(v_mctx_690_, 7);
v_eAssignment_706_ = lean_ctor_get(v_mctx_690_, 8);
v_dAssignment_707_ = lean_ctor_get(v_mctx_690_, 9);
v_instanceTypedMVars_708_ = lean_ctor_get(v_mctx_690_, 10);
v_synthNormMemo_709_ = lean_ctor_get(v_mctx_690_, 11);
v_isSharedCheck_723_ = !lean_is_exclusive(v_mctx_690_);
if (v_isSharedCheck_723_ == 0)
{
v___x_711_ = v_mctx_690_;
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_synthNormMemo_709_);
lean_inc(v_instanceTypedMVars_708_);
lean_inc(v_dAssignment_707_);
lean_inc(v_eAssignment_706_);
lean_inc(v_lAssignment_705_);
lean_inc(v_userNames_704_);
lean_inc(v_decls_703_);
lean_inc(v_lDecls_702_);
lean_inc(v_mvarCounter_701_);
lean_inc(v_lmvarCounter_700_);
lean_inc(v_levelAssignDepth_699_);
lean_inc(v_depth_698_);
lean_dec(v_mctx_690_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = lean_box(0);
v___x_714_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_eAssignment_706_, v_mvarId_685_, v_val_686_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 8, v___x_714_);
v___x_716_ = v___x_711_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_depth_698_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_levelAssignDepth_699_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_lmvarCounter_700_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_mvarCounter_701_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v_lDecls_702_);
lean_ctor_set(v_reuseFailAlloc_722_, 5, v_decls_703_);
lean_ctor_set(v_reuseFailAlloc_722_, 6, v_userNames_704_);
lean_ctor_set(v_reuseFailAlloc_722_, 7, v_lAssignment_705_);
lean_ctor_set(v_reuseFailAlloc_722_, 8, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_722_, 9, v_dAssignment_707_);
lean_ctor_set(v_reuseFailAlloc_722_, 10, v_instanceTypedMVars_708_);
lean_ctor_set(v_reuseFailAlloc_722_, 11, v_synthNormMemo_709_);
v___x_716_ = v_reuseFailAlloc_722_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_716_);
v___x_718_ = v___x_696_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_cache_691_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_zetaDeltaFVarIds_692_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_postponed_693_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_diag_694_);
v___x_718_ = v_reuseFailAlloc_721_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_st_ref_put(v___y_687_, v___x_718_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_713_);
return v___x_720_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_685_ = stack[0].m_obj;
lean_object* v_val_686_ = stack[1].m_obj;
lean_object* v___y_687_ = stack[2].m_obj;
lean_object* v_res_725_;
v_res_725_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_685_, v_val_686_, v___y_687_);
stack->m_obj
 = v_res_725_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg___boxed(lean_object* v_mvarId_726_, lean_object* v_val_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_726_, v_val_727_, v___y_728_);
lean_dec(v___y_728_);
return v_res_730_;
}
}
lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0(lean_object* v_mvarId_731_, lean_object* v_rule_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; 
lean_inc(v_mvarId_731_);
v___x_740_ = l_Lean_MVarId_getDecl(v_mvarId_731_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v_expr_742_; lean_object* v_pattern_743_; lean_object* v_resultPos_744_; lean_object* v_type_745_; uint8_t v___x_746_; lean_object* v___x_747_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v_expr_742_ = lean_ctor_get(v_rule_732_, 0);
lean_inc_ref(v_expr_742_);
v_pattern_743_ = lean_ctor_get(v_rule_732_, 1);
lean_inc_ref_n(v_pattern_743_, 2);
v_resultPos_744_ = lean_ctor_get(v_rule_732_, 2);
lean_inc(v_resultPos_744_);
lean_dec_ref(v_rule_732_);
v_type_745_ = lean_ctor_get(v_a_741_, 2);
lean_inc_ref(v_type_745_);
lean_dec(v_a_741_);
v___x_746_ = 1;
v___x_747_ = l_Lean_Meta_Sym_Pattern_unify_x3f(v_pattern_743_, v_type_745_, v___x_746_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_784_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_784_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_784_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_784_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
if (lean_obj_tag(v_a_748_) == 1)
{
lean_object* v_val_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_779_; 
v_val_752_ = lean_ctor_get(v_a_748_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_a_748_);
if (v_isSharedCheck_779_ == 0)
{
v___x_754_ = v_a_748_;
v_isShared_755_ = v_isSharedCheck_779_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_val_752_);
lean_dec(v_a_748_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_779_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_unresolvedInsts_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_unresolvedInsts_756_ = lean_ctor_get(v_val_752_, 2);
v___x_757_ = lean_array_get_size(v_unresolvedInsts_756_);
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = lean_nat_dec_eq(v___x_757_, v___x_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v___x_762_; 
lean_del_object(v___x_754_);
lean_dec(v_val_752_);
lean_dec(v_resultPos_744_);
lean_dec_ref(v_pattern_743_);
lean_dec_ref(v_expr_742_);
lean_dec(v_mvarId_731_);
v___x_760_ = lean_box(0);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_760_);
v___x_762_ = v___x_750_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_777_; 
lean_del_object(v___x_750_);
lean_inc(v_val_752_);
v___x_764_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(v_expr_742_, v_pattern_743_, v_val_752_);
v___x_765_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_731_, v___x_764_, v___y_736_);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v___x_765_, 0);
lean_dec(v_unused_778_);
v___x_767_ = v___x_765_;
v_isShared_768_ = v_isSharedCheck_777_;
goto v_resetjp_766_;
}
else
{
lean_dec(v___x_765_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_777_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_769_ = lean_box(0);
v___x_770_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(v_val_752_, v_resultPos_744_, v___x_769_);
lean_dec(v_val_752_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_770_);
v___x_772_ = v___x_754_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_776_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_774_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_772_);
v___x_774_ = v___x_767_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
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
}
else
{
lean_object* v___x_780_; lean_object* v___x_782_; 
lean_dec(v_a_748_);
lean_dec(v_resultPos_744_);
lean_dec_ref(v_pattern_743_);
lean_dec_ref(v_expr_742_);
lean_dec(v_mvarId_731_);
v___x_780_ = lean_box(0);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_780_);
v___x_782_ = v___x_750_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec(v_resultPos_744_);
lean_dec_ref(v_pattern_743_);
lean_dec_ref(v_expr_742_);
lean_dec(v_mvarId_731_);
v_a_785_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_747_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_747_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec_ref(v_rule_732_);
lean_dec(v_mvarId_731_);
v_a_793_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_740_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_740_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_BackwardRule_apply___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_731_ = stack[0].m_obj;
lean_object* v_rule_732_ = stack[1].m_obj;
lean_object* v___y_733_ = stack[2].m_obj;
lean_object* v___y_734_ = stack[3].m_obj;
lean_object* v___y_735_ = stack[4].m_obj;
lean_object* v___y_736_ = stack[5].m_obj;
lean_object* v___y_737_ = stack[6].m_obj;
lean_object* v___y_738_ = stack[7].m_obj;
lean_object* v_res_801_;
v_res_801_ = l_Lean_Meta_Sym_BackwardRule_apply___lam__0(v_mvarId_731_, v_rule_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
stack->m_obj
 = v_res_801_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed(lean_object* v_mvarId_802_, lean_object* v_rule_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_Meta_Sym_BackwardRule_apply___lam__0(v_mvarId_802_, v_rule_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
return v_res_811_;
}
}
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object* v_mvarId_812_, lean_object* v_rule_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___f_821_; lean_object* v___x_822_; 
lean_inc(v_mvarId_812_);
v___f_821_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed), 9, 2);
lean_closure_set(v___f_821_, 0, v_mvarId_812_);
lean_closure_set(v___f_821_, 1, v_rule_813_);
v___x_822_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(v_mvarId_812_, v___f_821_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
return v___x_822_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_BackwardRule_apply_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_812_ = stack[0].m_obj;
lean_object* v_rule_813_ = stack[1].m_obj;
lean_object* v_a_814_ = stack[2].m_obj;
lean_object* v_a_815_ = stack[3].m_obj;
lean_object* v_a_816_ = stack[4].m_obj;
lean_object* v_a_817_ = stack[5].m_obj;
lean_object* v_a_818_ = stack[6].m_obj;
lean_object* v_a_819_ = stack[7].m_obj;
lean_object* v_res_823_;
v_res_823_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_812_, v_rule_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
stack->m_obj
 = v_res_823_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply___boxed(lean_object* v_mvarId_824_, lean_object* v_rule_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_824_, v_rule_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
return v_res_833_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(lean_object* v_mvarId_834_, lean_object* v_val_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(v_mvarId_834_, v_val_835_, v___y_839_);
return v___x_843_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_834_ = stack[0].m_obj;
lean_object* v_val_835_ = stack[1].m_obj;
lean_object* v___y_836_ = stack[2].m_obj;
lean_object* v___y_837_ = stack[3].m_obj;
lean_object* v___y_838_ = stack[4].m_obj;
lean_object* v___y_839_ = stack[5].m_obj;
lean_object* v___y_840_ = stack[6].m_obj;
lean_object* v___y_841_ = stack[7].m_obj;
lean_object* v_res_844_;
v_res_844_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(v_mvarId_834_, v_val_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___boxed(lean_object* v_mvarId_845_, lean_object* v_val_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(v_mvarId_845_, v_val_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0(lean_object* v_00_u03b2_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_x_856_, v_x_857_, v_x_858_);
return v___x_859_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_860_, lean_object* v_x_861_, size_t v_x_862_, size_t v_x_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_861_, v_x_862_, v_x_863_, v_x_864_, v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_861_ = stack[1].m_obj;
size_t v_x_862_ = stack[2].m_num;
size_t v_x_863_ = stack[3].m_num;
lean_object* v_x_864_ = stack[4].m_obj;
lean_object* v_x_865_ = stack[5].m_obj;
lean_object* v_res_867_;
v_res_867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(lean_box(0), v_x_861_, v_x_862_, v_x_863_, v_x_864_, v_x_865_);
stack->m_obj
 = v_res_867_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_868_, lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
size_t v_x_3725__boxed_874_; size_t v_x_3726__boxed_875_; lean_object* v_res_876_; 
v_x_3725__boxed_874_ = lean_unbox_usize(v_x_870_);
lean_dec(v_x_870_);
v_x_3726__boxed_875_ = lean_unbox_usize(v_x_871_);
lean_dec(v_x_871_);
v_res_876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(v_00_u03b2_868_, v_x_869_, v_x_3725__boxed_874_, v_x_3726__boxed_875_, v_x_872_, v_x_873_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_877_, lean_object* v_n_878_, lean_object* v_k_879_, lean_object* v_v_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v_n_878_, v_k_879_, v_v_880_);
return v___x_881_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_882_, size_t v_depth_883_, lean_object* v_keys_884_, lean_object* v_vals_885_, lean_object* v_heq_886_, lean_object* v_i_887_, lean_object* v_entries_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_883_, v_keys_884_, v_vals_885_, v_i_887_, v_entries_888_);
return v___x_889_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_883_ = stack[1].m_num;
lean_object* v_keys_884_ = stack[2].m_obj;
lean_object* v_vals_885_ = stack[3].m_obj;
lean_object* v_i_887_ = stack[5].m_obj;
lean_object* v_entries_888_ = stack[6].m_obj;
lean_object* v_res_890_;
v_res_890_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(lean_box(0), v_depth_883_, v_keys_884_, v_vals_885_, lean_box(0), v_i_887_, v_entries_888_);
stack->m_obj
 = v_res_890_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_891_, lean_object* v_depth_892_, lean_object* v_keys_893_, lean_object* v_vals_894_, lean_object* v_heq_895_, lean_object* v_i_896_, lean_object* v_entries_897_){
_start:
{
size_t v_depth_boxed_898_; lean_object* v_res_899_; 
v_depth_boxed_898_ = lean_unbox_usize(v_depth_892_);
lean_dec(v_depth_892_);
v_res_899_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_891_, v_depth_boxed_898_, v_keys_893_, v_vals_894_, v_heq_895_, v_i_896_, v_entries_897_);
lean_dec_ref(v_vals_894_);
lean_dec_ref(v_keys_893_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_901_, v_x_902_, v_x_903_, v_x_904_);
return v___x_905_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(lean_object* v_msgData_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v___x_912_; lean_object* v_env_913_; uint8_t v___x_914_; lean_object* v_env_915_; lean_object* v___x_916_; lean_object* v_toCold_917_; lean_object* v_mctx_918_; lean_object* v_lctx_919_; lean_object* v_options_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_912_ = lean_st_ref_get(v___y_910_);
v_env_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc_ref(v_env_913_);
lean_dec(v___x_912_);
v___x_914_ = 0;
v_env_915_ = l_Lean_Environment_setRecordingDeps(v_env_913_, v___x_914_);
v___x_916_ = lean_st_ref_get(v___y_908_);
v_toCold_917_ = lean_ctor_get(v___y_909_, 0);
v_mctx_918_ = lean_ctor_get(v___x_916_, 0);
lean_inc_ref(v_mctx_918_);
lean_dec(v___x_916_);
v_lctx_919_ = lean_ctor_get(v___y_907_, 2);
v_options_920_ = lean_ctor_get(v_toCold_917_, 2);
lean_inc_ref(v_options_920_);
lean_inc_ref(v_lctx_919_);
v___x_921_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_921_, 0, v_env_915_);
lean_ctor_set(v___x_921_, 1, v_mctx_918_);
lean_ctor_set(v___x_921_, 2, v_lctx_919_);
lean_ctor_set(v___x_921_, 3, v_options_920_);
v___x_922_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v_msgData_906_);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_906_ = stack[0].m_obj;
lean_object* v___y_907_ = stack[1].m_obj;
lean_object* v___y_908_ = stack[2].m_obj;
lean_object* v___y_909_ = stack[3].m_obj;
lean_object* v___y_910_ = stack[4].m_obj;
lean_object* v_res_924_;
v_res_924_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msgData_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
stack->m_obj
 = v_res_924_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0___boxed(lean_object* v_msgData_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msgData_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
return v_res_931_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(lean_object* v_msg_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_ref_938_; lean_object* v___x_939_; lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
v_ref_938_ = lean_ctor_get(v___y_935_, 2);
v___x_939_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msg_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_948_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
lean_inc(v_ref_938_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v_ref_938_);
lean_ctor_set(v___x_944_, 1, v_a_940_);
if (v_isShared_943_ == 0)
{
lean_ctor_set_tag(v___x_942_, 1);
lean_ctor_set(v___x_942_, 0, v___x_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_932_ = stack[0].m_obj;
lean_object* v___y_933_ = stack[1].m_obj;
lean_object* v___y_934_ = stack[2].m_obj;
lean_object* v___y_935_ = stack[3].m_obj;
lean_object* v___y_936_ = stack[4].m_obj;
lean_object* v_res_949_;
v_res_949_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v_msg_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
stack->m_obj
 = v_res_949_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg___boxed(lean_object* v_msg_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v_msg_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_956_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27(lean_object* v_mvarId_963_, lean_object* v_rule_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_972_; 
lean_inc_ref(v_rule_964_);
lean_inc(v_mvarId_963_);
v___x_972_ = l_Lean_Meta_Sym_BackwardRule_apply(v_mvarId_963_, v_rule_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_990_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_990_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_990_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_990_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
if (lean_obj_tag(v_a_973_) == 1)
{
lean_object* v_mvarIds_977_; lean_object* v___x_979_; 
lean_dec_ref(v_rule_964_);
lean_dec(v_mvarId_963_);
v_mvarIds_977_ = lean_ctor_get(v_a_973_, 0);
lean_inc(v_mvarIds_977_);
lean_dec_ref_known(v_a_973_, 1);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_mvarIds_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_mvarIds_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
else
{
lean_object* v_expr_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_del_object(v___x_975_);
lean_dec(v_a_973_);
v_expr_981_ = lean_ctor_get(v_rule_964_, 0);
lean_inc_ref(v_expr_981_);
lean_dec_ref(v_rule_964_);
v___x_982_ = lean_obj_once(&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1, &l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1_once, _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1);
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v_mvarId_963_);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_obj_once(&l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3, &l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3_once, _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Lean_indentExpr(v_expr_981_);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v___x_988_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_989_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref(v_rule_964_);
lean_dec(v_mvarId_963_);
v_a_991_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_972_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_972_);
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
LEAN_EXPORT void l_Lean_Meta_Sym_BackwardRule_apply_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_963_ = stack[0].m_obj;
lean_object* v_rule_964_ = stack[1].m_obj;
lean_object* v_a_965_ = stack[2].m_obj;
lean_object* v_a_966_ = stack[3].m_obj;
lean_object* v_a_967_ = stack[4].m_obj;
lean_object* v_a_968_ = stack[5].m_obj;
lean_object* v_a_969_ = stack[6].m_obj;
lean_object* v_a_970_ = stack[7].m_obj;
lean_object* v_res_999_;
v_res_999_ = l_Lean_Meta_Sym_BackwardRule_apply_x27(v_mvarId_963_, v_rule_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
stack->m_obj
 = v_res_999_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_apply_x27___boxed(lean_object* v_mvarId_1000_, lean_object* v_rule_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_Meta_Sym_BackwardRule_apply_x27(v_mvarId_1000_, v_rule_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
return v_res_1009_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(lean_object* v_00_u03b1_1010_, lean_object* v_msg_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v_msg_1011_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1011_ = stack[1].m_obj;
lean_object* v___y_1012_ = stack[2].m_obj;
lean_object* v___y_1013_ = stack[3].m_obj;
lean_object* v___y_1014_ = stack[4].m_obj;
lean_object* v___y_1015_ = stack[5].m_obj;
lean_object* v___y_1016_ = stack[6].m_obj;
lean_object* v___y_1017_ = stack[7].m_obj;
lean_object* v_res_1020_;
v_res_1020_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(lean_box(0), v_msg_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
stack->m_obj
 = v_res_1020_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___boxed(lean_object* v_00_u03b1_1021_, lean_object* v_msg_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(v_00_u03b1_1021_, v_msg_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
return v_res_1030_;
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
