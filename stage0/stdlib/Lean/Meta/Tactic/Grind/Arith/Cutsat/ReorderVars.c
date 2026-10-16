// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.ReorderVars
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Lean.Meta.Tactic.Grind.Arith.Cutsat.EqCnstr import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr import Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default___redArg();
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_instBEqPoly_beq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "old2new: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reorder"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value;
static const lean_array_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "search"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value),LEAN_SCALAR_PTR_LITERAL(236, 159, 191, 181, 87, 7, 198, 44)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "new2old: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value),LEAN_SCALAR_PTR_LITERAL(144, 165, 104, 86, 70, 21, 218, 13)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "reordering variables, epoch: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(lean_object* v_a_5_, lean_object* v_x_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_9_; lean_object* v___y_11_; lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_9_ = lean_box(0);
v___x_14_ = lean_array_get_size(v_a_7_);
v___x_15_ = lean_nat_dec_lt(v_x_6_, v___x_14_);
if (v___x_15_ == 0)
{
lean_dec(v_a_5_);
v___y_11_ = v_a_7_;
goto v___jp_10_;
}
else
{
lean_object* v_v_16_; lean_object* v_maxLowerCoeff_17_; lean_object* v_maxUpperCoeff_18_; lean_object* v_maxDvdCoeff_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_31_; 
v_v_16_ = lean_array_fget(v_a_7_, v_x_6_);
v_maxLowerCoeff_17_ = lean_ctor_get(v_v_16_, 0);
v_maxUpperCoeff_18_ = lean_ctor_get(v_v_16_, 1);
v_maxDvdCoeff_19_ = lean_ctor_get(v_v_16_, 2);
v_isSharedCheck_31_ = !lean_is_exclusive(v_v_16_);
if (v_isSharedCheck_31_ == 0)
{
v___x_21_ = v_v_16_;
v_isShared_22_ = v_isSharedCheck_31_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_maxDvdCoeff_19_);
lean_inc(v_maxUpperCoeff_18_);
lean_inc(v_maxLowerCoeff_17_);
lean_dec(v_v_16_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_31_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v_xs_x27_23_; lean_object* v___y_25_; uint8_t v___x_30_; 
v_xs_x27_23_ = lean_array_fset(v_a_7_, v_x_6_, v___x_9_);
v___x_30_ = lean_nat_dec_le(v_a_5_, v_maxLowerCoeff_17_);
if (v___x_30_ == 0)
{
lean_dec(v_maxLowerCoeff_17_);
v___y_25_ = v_a_5_;
goto v___jp_24_;
}
else
{
lean_dec(v_a_5_);
v___y_25_ = v_maxLowerCoeff_17_;
goto v___jp_24_;
}
v___jp_24_:
{
lean_object* v___x_27_; 
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___y_25_);
v___x_27_ = v___x_21_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___y_25_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_maxUpperCoeff_18_);
lean_ctor_set(v_reuseFailAlloc_29_, 2, v_maxDvdCoeff_19_);
v___x_27_ = v_reuseFailAlloc_29_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; 
v___x_28_ = lean_array_fset(v_xs_x27_23_, v_x_6_, v___x_27_);
v___y_11_ = v___x_28_;
goto v___jp_10_;
}
}
}
}
v___jp_10_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_9_);
lean_ctor_set(v___x_12_, 1, v___y_11_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg___boxed(lean_object* v_a_32_, lean_object* v_x_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_32_, v_x_33_, v_a_34_);
lean_dec(v_x_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(lean_object* v_a_37_, lean_object* v_x_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_37_, v_x_38_, v_a_39_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___boxed(lean_object* v_a_52_, lean_object* v_x_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(v_a_52_, v_x_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec(v_a_55_);
lean_dec(v_x_53_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(lean_object* v_a_67_, lean_object* v_x_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_71_; lean_object* v___y_73_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_71_ = lean_box(0);
v___x_76_ = lean_array_get_size(v_a_69_);
v___x_77_ = lean_nat_dec_lt(v_x_68_, v___x_76_);
if (v___x_77_ == 0)
{
lean_dec(v_a_67_);
v___y_73_ = v_a_69_;
goto v___jp_72_;
}
else
{
lean_object* v_v_78_; lean_object* v_maxLowerCoeff_79_; lean_object* v_maxUpperCoeff_80_; lean_object* v_maxDvdCoeff_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_93_; 
v_v_78_ = lean_array_fget(v_a_69_, v_x_68_);
v_maxLowerCoeff_79_ = lean_ctor_get(v_v_78_, 0);
v_maxUpperCoeff_80_ = lean_ctor_get(v_v_78_, 1);
v_maxDvdCoeff_81_ = lean_ctor_get(v_v_78_, 2);
v_isSharedCheck_93_ = !lean_is_exclusive(v_v_78_);
if (v_isSharedCheck_93_ == 0)
{
v___x_83_ = v_v_78_;
v_isShared_84_ = v_isSharedCheck_93_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_maxDvdCoeff_81_);
lean_inc(v_maxUpperCoeff_80_);
lean_inc(v_maxLowerCoeff_79_);
lean_dec(v_v_78_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_93_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v_xs_x27_85_; lean_object* v___y_87_; uint8_t v___x_92_; 
v_xs_x27_85_ = lean_array_fset(v_a_69_, v_x_68_, v___x_71_);
v___x_92_ = lean_nat_dec_le(v_a_67_, v_maxUpperCoeff_80_);
if (v___x_92_ == 0)
{
lean_dec(v_maxUpperCoeff_80_);
v___y_87_ = v_a_67_;
goto v___jp_86_;
}
else
{
lean_dec(v_a_67_);
v___y_87_ = v_maxUpperCoeff_80_;
goto v___jp_86_;
}
v___jp_86_:
{
lean_object* v___x_89_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v___y_87_);
v___x_89_ = v___x_83_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_maxLowerCoeff_79_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___y_87_);
lean_ctor_set(v_reuseFailAlloc_91_, 2, v_maxDvdCoeff_81_);
v___x_89_ = v_reuseFailAlloc_91_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; 
v___x_90_ = lean_array_fset(v_xs_x27_85_, v_x_68_, v___x_89_);
v___y_73_ = v___x_90_;
goto v___jp_72_;
}
}
}
}
v___jp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_71_);
lean_ctor_set(v___x_74_, 1, v___y_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg___boxed(lean_object* v_a_94_, lean_object* v_x_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_94_, v_x_95_, v_a_96_);
lean_dec(v_x_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(lean_object* v_a_99_, lean_object* v_x_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_99_, v_x_100_, v_a_101_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___boxed(lean_object* v_a_114_, lean_object* v_x_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(v_a_114_, v_x_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec(v_a_117_);
lean_dec(v_x_115_);
return v_res_128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_nat_to_int(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(lean_object* v_a_131_, lean_object* v_x_132_, lean_object* v_a_133_){
_start:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0);
v___x_136_ = lean_int_dec_lt(v_a_131_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_nat_abs(v_a_131_);
v___x_138_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v___x_137_, v_x_132_, v_a_133_);
return v___x_138_;
}
else
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_nat_abs(v_a_131_);
v___x_140_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v___x_139_, v_x_132_, v_a_133_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___boxed(lean_object* v_a_141_, lean_object* v_x_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_141_, v_x_142_, v_a_143_);
lean_dec(v_x_142_);
lean_dec(v_a_141_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(lean_object* v_a_146_, lean_object* v_x_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_146_, v_x_147_, v_a_148_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___boxed(lean_object* v_a_161_, lean_object* v_x_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(v_a_161_, v_x_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec(v_a_164_);
lean_dec(v_x_162_);
lean_dec(v_a_161_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(lean_object* v_a_176_, lean_object* v_x_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_180_; lean_object* v___y_182_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_180_ = lean_box(0);
v___x_185_ = lean_array_get_size(v_a_178_);
v___x_186_ = lean_nat_dec_lt(v_x_177_, v___x_185_);
if (v___x_186_ == 0)
{
lean_dec(v_a_176_);
v___y_182_ = v_a_178_;
goto v___jp_181_;
}
else
{
lean_object* v_v_187_; lean_object* v_maxLowerCoeff_188_; lean_object* v_maxUpperCoeff_189_; lean_object* v_maxDvdCoeff_190_; lean_object* v_xs_x27_191_; uint8_t v___x_192_; 
v_v_187_ = lean_array_fget(v_a_178_, v_x_177_);
v_maxLowerCoeff_188_ = lean_ctor_get(v_v_187_, 0);
v_maxUpperCoeff_189_ = lean_ctor_get(v_v_187_, 1);
v_maxDvdCoeff_190_ = lean_ctor_get(v_v_187_, 2);
v_xs_x27_191_ = lean_array_fset(v_a_178_, v_x_177_, v___x_180_);
v___x_192_ = lean_nat_dec_le(v_a_176_, v_maxDvdCoeff_190_);
if (v___x_192_ == 0)
{
lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_200_; 
lean_inc(v_maxUpperCoeff_189_);
lean_inc(v_maxLowerCoeff_188_);
v_isSharedCheck_200_ = !lean_is_exclusive(v_v_187_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; lean_object* v_unused_202_; lean_object* v_unused_203_; 
v_unused_201_ = lean_ctor_get(v_v_187_, 2);
lean_dec(v_unused_201_);
v_unused_202_ = lean_ctor_get(v_v_187_, 1);
lean_dec(v_unused_202_);
v_unused_203_ = lean_ctor_get(v_v_187_, 0);
lean_dec(v_unused_203_);
v___x_194_ = v_v_187_;
v_isShared_195_ = v_isSharedCheck_200_;
goto v_resetjp_193_;
}
else
{
lean_dec(v_v_187_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_200_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 2, v_a_176_);
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_maxLowerCoeff_188_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_maxUpperCoeff_189_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_a_176_);
v___x_197_ = v_reuseFailAlloc_199_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; 
v___x_198_ = lean_array_fset(v_xs_x27_191_, v_x_177_, v___x_197_);
v___y_182_ = v___x_198_;
goto v___jp_181_;
}
}
}
else
{
lean_object* v___x_204_; 
lean_dec(v_a_176_);
v___x_204_ = lean_array_fset(v_xs_x27_191_, v_x_177_, v_v_187_);
v___y_182_ = v___x_204_;
goto v___jp_181_;
}
}
v___jp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_180_);
lean_ctor_set(v___x_183_, 1, v___y_182_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg___boxed(lean_object* v_a_205_, lean_object* v_x_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_205_, v_x_206_, v_a_207_);
lean_dec(v_x_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(lean_object* v_a_210_, lean_object* v_x_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_210_, v_x_211_, v_a_212_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___boxed(lean_object* v_a_225_, lean_object* v_x_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(v_a_225_, v_x_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec(v_a_228_);
lean_dec(v_x_226_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
if (lean_obj_tag(v_a_240_) == 0)
{
lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_251_; 
v_isSharedCheck_251_ = !lean_is_exclusive(v_a_240_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v_a_240_, 0);
lean_dec(v_unused_252_);
v___x_244_ = v_a_240_;
v_isShared_245_ = v_isSharedCheck_251_;
goto v_resetjp_243_;
}
else
{
lean_dec(v_a_240_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_251_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_246_ = lean_box(0);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v_a_241_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_247_);
v___x_249_ = v___x_244_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_object* v_k_253_; lean_object* v_v_254_; lean_object* v_p_255_; lean_object* v___x_256_; lean_object* v_a_257_; lean_object* v_snd_258_; 
v_k_253_ = lean_ctor_get(v_a_240_, 0);
lean_inc(v_k_253_);
v_v_254_ = lean_ctor_get(v_a_240_, 1);
lean_inc(v_v_254_);
v_p_255_ = lean_ctor_get(v_a_240_, 2);
lean_inc_ref(v_p_255_);
lean_dec_ref_known(v_a_240_, 3);
v___x_256_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_k_253_, v_v_254_, v_a_241_);
lean_dec(v_v_254_);
lean_dec(v_k_253_);
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
lean_dec_ref(v___x_256_);
v_snd_258_ = lean_ctor_get(v_a_257_, 1);
lean_inc(v_snd_258_);
lean_dec(v_a_257_);
v_a_240_ = v_p_255_;
v_a_241_ = v_snd_258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg___boxed(lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_260_, v_a_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_264_, v_a_265_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___boxed(lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec(v_a_280_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(lean_object* v_as_295_, size_t v_sz_296_, size_t v_i_297_, lean_object* v_b_298_, lean_object* v___y_299_){
_start:
{
uint8_t v___x_301_; 
v___x_301_ = lean_usize_dec_lt(v_i_297_, v_sz_296_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v_b_298_);
lean_ctor_set(v___x_302_, 1, v___y_299_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
else
{
lean_object* v_a_304_; lean_object* v_p_305_; lean_object* v___x_306_; 
lean_dec_ref(v_b_298_);
v_a_304_ = lean_array_uget_borrowed(v_as_295_, v_i_297_);
v_p_305_ = lean_ctor_get(v_a_304_, 0);
lean_inc_ref(v_p_305_);
v___x_306_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_305_, v___y_299_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v_snd_308_; lean_object* v___x_309_; size_t v___x_310_; size_t v___x_311_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_306_, 1);
v_snd_308_ = lean_ctor_get(v_a_307_, 1);
lean_inc(v_snd_308_);
lean_dec(v_a_307_);
v___x_309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_310_ = ((size_t)1ULL);
v___x_311_ = lean_usize_add(v_i_297_, v___x_310_);
v_i_297_ = v___x_311_;
v_b_298_ = v___x_309_;
v___y_299_ = v_snd_308_;
goto _start;
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_a_313_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_306_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_306_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_321_, lean_object* v_sz_322_, lean_object* v_i_323_, lean_object* v_b_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
size_t v_sz_boxed_327_; size_t v_i_boxed_328_; lean_object* v_res_329_; 
v_sz_boxed_327_ = lean_unbox_usize(v_sz_322_);
lean_dec(v_sz_322_);
v_i_boxed_328_ = lean_unbox_usize(v_i_323_);
lean_dec(v_i_323_);
v_res_329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_321_, v_sz_boxed_327_, v_i_boxed_328_, v_b_324_, v___y_325_);
lean_dec_ref(v_as_321_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(lean_object* v_as_330_, size_t v_sz_331_, size_t v_i_332_, lean_object* v_b_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = lean_usize_dec_lt(v_i_332_, v_sz_331_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v_b_333_);
lean_ctor_set(v___x_347_, 1, v___y_334_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
else
{
lean_object* v_a_349_; lean_object* v_p_350_; lean_object* v___x_351_; 
lean_dec_ref(v_b_333_);
v_a_349_ = lean_array_uget_borrowed(v_as_330_, v_i_332_);
v_p_350_ = lean_ctor_get(v_a_349_, 0);
lean_inc_ref(v_p_350_);
v___x_351_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_350_, v___y_334_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v_snd_353_; lean_object* v___x_354_; size_t v___x_355_; size_t v___x_356_; lean_object* v___x_357_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
v_snd_353_ = lean_ctor_get(v_a_352_, 1);
lean_inc(v_snd_353_);
lean_dec(v_a_352_);
v___x_354_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_355_ = ((size_t)1ULL);
v___x_356_ = lean_usize_add(v_i_332_, v___x_355_);
v___x_357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_330_, v_sz_331_, v___x_356_, v___x_354_, v_snd_353_);
return v___x_357_;
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
v_a_358_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_351_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_351_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1___boxed(lean_object* v_as_366_, lean_object* v_sz_367_, lean_object* v_i_368_, lean_object* v_b_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
size_t v_sz_boxed_382_; size_t v_i_boxed_383_; lean_object* v_res_384_; 
v_sz_boxed_382_ = lean_unbox_usize(v_sz_367_);
lean_dec(v_sz_367_);
v_i_boxed_383_ = lean_unbox_usize(v_i_368_);
lean_dec(v_i_368_);
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_as_366_, v_sz_boxed_382_, v_i_boxed_383_, v_b_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v_as_366_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_as_388_, size_t v_sz_389_, size_t v_i_390_, lean_object* v_b_391_, lean_object* v___y_392_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = lean_usize_dec_lt(v_i_390_, v_sz_389_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v_b_391_);
lean_ctor_set(v___x_395_, 1, v___y_392_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
else
{
lean_object* v_a_397_; lean_object* v_p_398_; lean_object* v___x_399_; 
lean_dec_ref(v_b_391_);
v_a_397_ = lean_array_uget_borrowed(v_as_388_, v_i_390_);
v_p_398_ = lean_ctor_get(v_a_397_, 0);
lean_inc_ref(v_p_398_);
v___x_399_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_398_, v___y_392_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v_snd_401_; lean_object* v___x_402_; size_t v___x_403_; size_t v___x_404_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_399_, 1);
v_snd_401_ = lean_ctor_get(v_a_400_, 1);
lean_inc(v_snd_401_);
lean_dec(v_a_400_);
v___x_402_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_add(v_i_390_, v___x_403_);
v_i_390_ = v___x_404_;
v_b_391_ = v___x_402_;
v___y_392_ = v_snd_401_;
goto _start;
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
v_a_406_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_399_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_399_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_as_414_, lean_object* v_sz_415_, lean_object* v_i_416_, lean_object* v_b_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
size_t v_sz_boxed_420_; size_t v_i_boxed_421_; lean_object* v_res_422_; 
v_sz_boxed_420_ = lean_unbox_usize(v_sz_415_);
lean_dec(v_sz_415_);
v_i_boxed_421_ = lean_unbox_usize(v_i_416_);
lean_dec(v_i_416_);
v_res_422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_414_, v_sz_boxed_420_, v_i_boxed_421_, v_b_417_, v___y_418_);
lean_dec_ref(v_as_414_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(lean_object* v_as_423_, size_t v_sz_424_, size_t v_i_425_, lean_object* v_b_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
uint8_t v___x_439_; 
v___x_439_ = lean_usize_dec_lt(v_i_425_, v_sz_424_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_b_426_);
lean_ctor_set(v___x_440_, 1, v___y_427_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
else
{
lean_object* v_a_442_; lean_object* v_p_443_; lean_object* v___x_444_; 
lean_dec_ref(v_b_426_);
v_a_442_ = lean_array_uget_borrowed(v_as_423_, v_i_425_);
v_p_443_ = lean_ctor_get(v_a_442_, 0);
lean_inc_ref(v_p_443_);
v___x_444_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_443_, v___y_427_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v_snd_446_; lean_object* v___x_447_; size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
v_snd_446_ = lean_ctor_get(v_a_445_, 1);
lean_inc(v_snd_446_);
lean_dec(v_a_445_);
v___x_447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_i_425_, v___x_448_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_423_, v_sz_424_, v___x_449_, v___x_447_, v_snd_446_);
return v___x_450_;
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_a_451_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_444_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_444_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2___boxed(lean_object* v_as_459_, lean_object* v_sz_460_, lean_object* v_i_461_, lean_object* v_b_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
size_t v_sz_boxed_475_; size_t v_i_boxed_476_; lean_object* v_res_477_; 
v_sz_boxed_475_ = lean_unbox_usize(v_sz_460_);
lean_dec(v_sz_460_);
v_i_boxed_476_ = lean_unbox_usize(v_i_461_);
lean_dec(v_i_461_);
v_res_477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_as_459_, v_sz_boxed_475_, v_i_boxed_476_, v_b_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v_as_459_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(lean_object* v_init_478_, lean_object* v_n_479_, lean_object* v_b_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
if (lean_obj_tag(v_n_479_) == 0)
{
lean_object* v_cs_493_; lean_object* v___x_494_; lean_object* v___x_495_; size_t v_sz_496_; size_t v___x_497_; lean_object* v___x_498_; 
v_cs_493_ = lean_ctor_get(v_n_479_, 0);
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_b_480_);
v_sz_496_ = lean_array_size(v_cs_493_);
v___x_497_ = ((size_t)0ULL);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_478_, v_cs_493_, v_sz_496_, v___x_497_, v___x_495_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_533_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_533_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_533_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_533_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v_fst_503_; lean_object* v_fst_504_; 
v_fst_503_ = lean_ctor_get(v_a_499_, 0);
lean_inc(v_fst_503_);
v_fst_504_ = lean_ctor_get(v_fst_503_, 0);
if (lean_obj_tag(v_fst_504_) == 0)
{
lean_object* v_snd_505_; lean_object* v_snd_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_517_; 
v_snd_505_ = lean_ctor_get(v_a_499_, 1);
lean_inc(v_snd_505_);
lean_dec(v_a_499_);
v_snd_506_ = lean_ctor_get(v_fst_503_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_fst_503_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v_fst_503_, 0);
lean_dec(v_unused_518_);
v___x_508_ = v_fst_503_;
v_isShared_509_ = v_isSharedCheck_517_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snd_506_);
lean_dec(v_fst_503_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_517_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v_snd_506_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_snd_505_);
lean_ctor_set(v___x_508_, 0, v___x_510_);
v___x_512_ = v___x_508_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_snd_505_);
v___x_512_ = v_reuseFailAlloc_516_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_512_);
v___x_514_ = v___x_501_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_530_; 
lean_inc_ref(v_fst_504_);
v_isSharedCheck_530_ = !lean_is_exclusive(v_fst_503_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; lean_object* v_unused_532_; 
v_unused_531_ = lean_ctor_get(v_fst_503_, 1);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_fst_503_, 0);
lean_dec(v_unused_532_);
v___x_520_ = v_fst_503_;
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
else
{
lean_dec(v_fst_503_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_snd_522_; lean_object* v_val_523_; lean_object* v___x_525_; 
v_snd_522_ = lean_ctor_get(v_a_499_, 1);
lean_inc(v_snd_522_);
lean_dec(v_a_499_);
v_val_523_ = lean_ctor_get(v_fst_504_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v_fst_504_, 1);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v_snd_522_);
lean_ctor_set(v___x_520_, 0, v_val_523_);
v___x_525_ = v___x_520_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_val_523_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_snd_522_);
v___x_525_ = v_reuseFailAlloc_529_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_527_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_525_);
v___x_527_ = v___x_501_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v_a_534_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_498_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_498_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_object* v_vs_542_; lean_object* v___x_543_; lean_object* v___x_544_; size_t v_sz_545_; size_t v___x_546_; lean_object* v___x_547_; 
v_vs_542_ = lean_ctor_get(v_n_479_, 0);
v___x_543_ = lean_box(0);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v_b_480_);
v_sz_545_ = lean_array_size(v_vs_542_);
v___x_546_ = ((size_t)0ULL);
v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_vs_542_, v_sz_545_, v___x_546_, v___x_544_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_582_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_582_ == 0)
{
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_582_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_582_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_fst_552_; lean_object* v_fst_553_; 
v_fst_552_ = lean_ctor_get(v_a_548_, 0);
lean_inc(v_fst_552_);
v_fst_553_ = lean_ctor_get(v_fst_552_, 0);
if (lean_obj_tag(v_fst_553_) == 0)
{
lean_object* v_snd_554_; lean_object* v_snd_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_566_; 
v_snd_554_ = lean_ctor_get(v_a_548_, 1);
lean_inc(v_snd_554_);
lean_dec(v_a_548_);
v_snd_555_ = lean_ctor_get(v_fst_552_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_fst_552_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; 
v_unused_567_ = lean_ctor_get(v_fst_552_, 0);
lean_dec(v_unused_567_);
v___x_557_ = v_fst_552_;
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_snd_555_);
lean_dec(v_fst_552_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v_snd_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v_snd_554_);
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_snd_554_);
v___x_561_ = v_reuseFailAlloc_565_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_563_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_561_);
v___x_563_ = v___x_550_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_579_; 
lean_inc_ref(v_fst_553_);
v_isSharedCheck_579_ = !lean_is_exclusive(v_fst_552_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; lean_object* v_unused_581_; 
v_unused_580_ = lean_ctor_get(v_fst_552_, 1);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_fst_552_, 0);
lean_dec(v_unused_581_);
v___x_569_ = v_fst_552_;
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
else
{
lean_dec(v_fst_552_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_snd_571_; lean_object* v_val_572_; lean_object* v___x_574_; 
v_snd_571_ = lean_ctor_get(v_a_548_, 1);
lean_inc(v_snd_571_);
lean_dec(v_a_548_);
v_val_572_ = lean_ctor_get(v_fst_553_, 0);
lean_inc(v_val_572_);
lean_dec_ref_known(v_fst_553_, 1);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 1, v_snd_571_);
lean_ctor_set(v___x_569_, 0, v_val_572_);
v___x_574_ = v___x_569_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_val_572_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_snd_571_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_574_);
v___x_576_ = v___x_550_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
v_a_583_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_547_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_547_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(lean_object* v_init_591_, lean_object* v_as_592_, size_t v_sz_593_, size_t v_i_594_, lean_object* v_b_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
uint8_t v___x_608_; 
v___x_608_ = lean_usize_dec_lt(v_i_594_, v_sz_593_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v_b_595_);
lean_ctor_set(v___x_609_, 1, v___y_596_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
else
{
lean_object* v_snd_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_661_; 
v_snd_611_ = lean_ctor_get(v_b_595_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_b_595_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v_b_595_, 0);
lean_dec(v_unused_662_);
v___x_613_ = v_b_595_;
v_isShared_614_ = v_isSharedCheck_661_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_snd_611_);
lean_dec(v_b_595_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_661_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v_a_616_; lean_object* v___x_617_; 
v___x_615_ = lean_box(0);
v_a_616_ = lean_array_uget_borrowed(v_as_592_, v_i_594_);
lean_inc(v_snd_611_);
v___x_617_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_591_, v_a_616_, v_snd_611_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_652_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_652_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_652_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_652_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_fst_622_; 
v_fst_622_ = lean_ctor_get(v_a_618_, 0);
lean_inc(v_fst_622_);
if (lean_obj_tag(v_fst_622_) == 0)
{
lean_object* v_snd_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_637_; 
v_snd_623_ = lean_ctor_get(v_a_618_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v_a_618_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; 
v_unused_638_ = lean_ctor_get(v_a_618_, 0);
lean_dec(v_unused_638_);
v___x_625_ = v_a_618_;
v_isShared_626_ = v_isSharedCheck_637_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_snd_623_);
lean_dec(v_a_618_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_637_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v_fst_622_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v_snd_611_);
lean_ctor_set(v___x_625_, 0, v___x_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_snd_611_);
v___x_629_ = v_reuseFailAlloc_636_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v_snd_623_);
lean_ctor_set(v___x_613_, 0, v___x_629_);
v___x_631_ = v___x_613_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_snd_623_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_631_);
v___x_633_ = v___x_620_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
else
{
lean_object* v_snd_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_650_; 
lean_del_object(v___x_620_);
lean_del_object(v___x_613_);
lean_dec(v_snd_611_);
v_snd_639_ = lean_ctor_get(v_a_618_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_a_618_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v_a_618_, 0);
lean_dec(v_unused_651_);
v___x_641_ = v_a_618_;
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_snd_639_);
lean_dec(v_a_618_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_a_643_; lean_object* v___x_645_; 
v_a_643_ = lean_ctor_get(v_fst_622_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v_fst_622_, 1);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v_a_643_);
lean_ctor_set(v___x_641_, 0, v___x_615_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_a_643_);
v___x_645_ = v_reuseFailAlloc_649_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
size_t v___x_646_; size_t v___x_647_; 
v___x_646_ = ((size_t)1ULL);
v___x_647_ = lean_usize_add(v_i_594_, v___x_646_);
v_i_594_ = v___x_647_;
v_b_595_ = v___x_645_;
v___y_596_ = v_snd_639_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_del_object(v___x_613_);
lean_dec(v_snd_611_);
v_a_653_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_617_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_617_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_663_ = _args[0];
lean_object* v_as_664_ = _args[1];
lean_object* v_sz_665_ = _args[2];
lean_object* v_i_666_ = _args[3];
lean_object* v_b_667_ = _args[4];
lean_object* v___y_668_ = _args[5];
lean_object* v___y_669_ = _args[6];
lean_object* v___y_670_ = _args[7];
lean_object* v___y_671_ = _args[8];
lean_object* v___y_672_ = _args[9];
lean_object* v___y_673_ = _args[10];
lean_object* v___y_674_ = _args[11];
lean_object* v___y_675_ = _args[12];
lean_object* v___y_676_ = _args[13];
lean_object* v___y_677_ = _args[14];
lean_object* v___y_678_ = _args[15];
lean_object* v___y_679_ = _args[16];
_start:
{
size_t v_sz_boxed_680_; size_t v_i_boxed_681_; lean_object* v_res_682_; 
v_sz_boxed_680_ = lean_unbox_usize(v_sz_665_);
lean_dec(v_sz_665_);
v_i_boxed_681_ = lean_unbox_usize(v_i_666_);
lean_dec(v_i_666_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_663_, v_as_664_, v_sz_boxed_680_, v_i_boxed_681_, v_b_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v_as_664_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0___boxed(lean_object* v_init_683_, lean_object* v_n_684_, lean_object* v_b_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_683_, v_n_684_, v_b_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v_n_684_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(lean_object* v_t_699_, lean_object* v_init_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_b_714_; lean_object* v___y_715_; lean_object* v_root_718_; lean_object* v_tail_719_; lean_object* v___x_720_; 
v_root_718_ = lean_ctor_get(v_t_699_, 0);
v_tail_719_ = lean_ctor_get(v_t_699_, 1);
v___x_720_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_700_, v_root_718_, v_init_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v_fst_722_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_720_, 1);
v_fst_722_ = lean_ctor_get(v_a_721_, 0);
lean_inc(v_fst_722_);
if (lean_obj_tag(v_fst_722_) == 0)
{
lean_object* v_snd_723_; lean_object* v_a_724_; 
v_snd_723_ = lean_ctor_get(v_a_721_, 1);
lean_inc(v_snd_723_);
lean_dec(v_a_721_);
v_a_724_ = lean_ctor_get(v_fst_722_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v_fst_722_, 1);
v_b_714_ = v_a_724_;
v___y_715_ = v_snd_723_;
goto v___jp_713_;
}
else
{
lean_object* v_snd_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_767_; 
v_snd_725_ = lean_ctor_get(v_a_721_, 1);
v_isSharedCheck_767_ = !lean_is_exclusive(v_a_721_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; 
v_unused_768_ = lean_ctor_get(v_a_721_, 0);
lean_dec(v_unused_768_);
v___x_727_ = v_a_721_;
v_isShared_728_ = v_isSharedCheck_767_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_snd_725_);
lean_dec(v_a_721_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_767_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v_a_729_ = lean_ctor_get(v_fst_722_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v_fst_722_, 1);
v___x_730_ = lean_box(0);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v_a_729_);
lean_ctor_set(v___x_727_, 0, v___x_730_);
v___x_732_ = v___x_727_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_a_729_);
v___x_732_ = v_reuseFailAlloc_766_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
size_t v_sz_733_; size_t v___x_734_; lean_object* v___x_735_; 
v_sz_733_ = lean_array_size(v_tail_719_);
v___x_734_ = ((size_t)0ULL);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_tail_719_, v_sz_733_, v___x_734_, v___x_732_, v_snd_725_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_757_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_757_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_757_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_757_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_fst_740_; lean_object* v_fst_741_; 
v_fst_740_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_fst_740_);
v_fst_741_ = lean_ctor_get(v_fst_740_, 0);
if (lean_obj_tag(v_fst_741_) == 0)
{
lean_object* v_snd_742_; lean_object* v_snd_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_753_; 
v_snd_742_ = lean_ctor_get(v_a_736_, 1);
lean_inc(v_snd_742_);
lean_dec(v_a_736_);
v_snd_743_ = lean_ctor_get(v_fst_740_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_fst_740_);
if (v_isSharedCheck_753_ == 0)
{
lean_object* v_unused_754_; 
v_unused_754_ = lean_ctor_get(v_fst_740_, 0);
lean_dec(v_unused_754_);
v___x_745_ = v_fst_740_;
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_snd_743_);
lean_dec(v_fst_740_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v_snd_742_);
lean_ctor_set(v___x_745_, 0, v_snd_743_);
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_snd_743_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_snd_742_);
v___x_748_ = v_reuseFailAlloc_752_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_750_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_748_);
v___x_750_ = v___x_738_;
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
else
{
lean_object* v_snd_755_; lean_object* v_val_756_; 
lean_inc_ref(v_fst_741_);
lean_dec(v_fst_740_);
lean_del_object(v___x_738_);
v_snd_755_ = lean_ctor_get(v_a_736_, 1);
lean_inc(v_snd_755_);
lean_dec(v_a_736_);
v_val_756_ = lean_ctor_get(v_fst_741_, 0);
lean_inc(v_val_756_);
lean_dec_ref_known(v_fst_741_, 1);
v_b_714_ = v_val_756_;
v___y_715_ = v_snd_755_;
goto v___jp_713_;
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
v_a_758_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_735_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_735_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
v_a_769_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_720_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_720_);
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
v___jp_713_:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v_b_714_);
lean_ctor_set(v___x_716_, 1, v___y_715_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0___boxed(lean_object* v_t_777_, lean_object* v_init_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v_t_777_, v_init_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v_t_777_);
return v_res_791_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(lean_object* v_xs_792_, lean_object* v_i_793_){
_start:
{
lean_object* v_size_794_; uint8_t v___x_795_; 
v_size_794_ = lean_ctor_get(v_xs_792_, 2);
v___x_795_ = lean_nat_dec_lt(v_i_793_, v_size_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0___boxed(lean_object* v_xs_796_, lean_object* v_i_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_xs_796_, v_i_797_);
lean_dec(v_i_797_);
lean_dec_ref(v_xs_796_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(lean_object* v_a_801_, lean_object* v_range_802_, lean_object* v_b_803_, lean_object* v_i_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_stop_817_; lean_object* v_step_818_; uint8_t v___x_819_; 
v_stop_817_ = lean_ctor_get(v_range_802_, 1);
v_step_818_ = lean_ctor_get(v_range_802_, 2);
v___x_819_ = lean_nat_dec_lt(v_i_804_, v_stop_817_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec(v_i_804_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_b_803_);
lean_ctor_set(v___x_820_, 1, v___y_805_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; lean_object* v_snd_824_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___x_836_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_822_ = lean_box(0);
v___x_836_ = lean_box(0);
v___x_848_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0);
v___x_849_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_i_804_, v___y_806_, v___y_814_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; uint8_t v___x_851_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
v___x_851_ = lean_unbox(v_a_850_);
lean_dec(v_a_850_);
if (v___x_851_ == 0)
{
lean_object* v_lowers_852_; lean_object* v_uppers_853_; lean_object* v___y_855_; uint8_t v___x_862_; 
v_lowers_852_ = lean_ctor_get(v_a_801_, 6);
v_uppers_853_ = lean_ctor_get(v_a_801_, 7);
v___x_862_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_lowers_852_, v_i_804_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
v___x_863_ = l_outOfBounds___redArg(v___x_848_);
v___y_855_ = v___x_863_;
goto v___jp_854_;
}
else
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_PersistentArray_get_x21___redArg(v___x_848_, v_lowers_852_, v_i_804_);
v___y_855_ = v___x_864_;
goto v___jp_854_;
}
v___jp_854_:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_855_, v___x_822_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec_ref(v___y_855_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v_snd_858_; uint8_t v___x_859_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
v_snd_858_ = lean_ctor_get(v_a_857_, 1);
lean_inc(v_snd_858_);
lean_dec(v_a_857_);
v___x_859_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_uppers_853_, v_i_804_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
v___x_860_ = l_outOfBounds___redArg(v___x_848_);
v___y_838_ = v_snd_858_;
v___y_839_ = v___x_860_;
goto v___jp_837_;
}
else
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentArray_get_x21___redArg(v___x_848_, v_uppers_853_, v_i_804_);
v___y_838_ = v_snd_858_;
v___y_839_ = v___x_861_;
goto v___jp_837_;
}
}
else
{
lean_dec(v_i_804_);
return v___x_856_;
}
}
}
else
{
v_snd_824_ = v___y_805_;
goto v___jp_823_;
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v___y_805_);
lean_dec(v_i_804_);
v_a_865_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_849_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_849_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
v___jp_823_:
{
lean_object* v___x_825_; 
v___x_825_ = lean_nat_add(v_i_804_, v_step_818_);
lean_dec(v_i_804_);
v_b_803_ = v___x_822_;
v_i_804_ = v___x_825_;
v___y_805_ = v_snd_824_;
goto _start;
}
v___jp_827_:
{
if (lean_obj_tag(v___y_829_) == 1)
{
lean_object* v_val_830_; lean_object* v_d_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v_a_834_; lean_object* v_snd_835_; 
v_val_830_ = lean_ctor_get(v___y_829_, 0);
lean_inc(v_val_830_);
lean_dec_ref_known(v___y_829_, 1);
v_d_831_ = lean_ctor_get(v_val_830_, 0);
lean_inc(v_d_831_);
lean_dec(v_val_830_);
v___x_832_ = lean_nat_abs(v_d_831_);
lean_dec(v_d_831_);
v___x_833_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v___x_832_, v_i_804_, v___y_828_);
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref(v___x_833_);
v_snd_835_ = lean_ctor_get(v_a_834_, 1);
lean_inc(v_snd_835_);
lean_dec(v_a_834_);
v_snd_824_ = v_snd_835_;
goto v___jp_823_;
}
else
{
lean_dec(v___y_829_);
v_snd_824_ = v___y_828_;
goto v___jp_823_;
}
}
v___jp_837_:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_839_, v___x_822_, v___y_838_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec_ref(v___y_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v_dvds_842_; lean_object* v_snd_843_; lean_object* v_size_844_; uint8_t v___x_845_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_840_, 1);
v_dvds_842_ = lean_ctor_get(v_a_801_, 5);
v_snd_843_ = lean_ctor_get(v_a_841_, 1);
lean_inc(v_snd_843_);
lean_dec(v_a_841_);
v_size_844_ = lean_ctor_get(v_dvds_842_, 2);
v___x_845_ = lean_nat_dec_lt(v_i_804_, v_size_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; 
v___x_846_ = l_outOfBounds___redArg(v___x_836_);
v___y_828_ = v_snd_843_;
v___y_829_ = v___x_846_;
goto v___jp_827_;
}
else
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentArray_get_x21___redArg(v___x_836_, v_dvds_842_, v_i_804_);
v___y_828_ = v_snd_843_;
v___y_829_ = v___x_847_;
goto v___jp_827_;
}
}
else
{
lean_dec(v_i_804_);
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___boxed(lean_object* v_a_873_, lean_object* v_range_874_, lean_object* v_b_875_, lean_object* v_i_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_873_, v_range_874_, v_b_875_, v_i_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v_range_874_);
lean_dec_ref(v_a_873_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_891_, v_a_899_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v_vars_904_; lean_object* v_size_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
v_vars_904_ = lean_ctor_get(v_a_903_, 0);
v_size_905_ = lean_ctor_get(v_vars_904_, 2);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_unsigned_to_nat(1u);
lean_inc(v_size_905_);
v___x_908_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v_size_905_);
lean_ctor_set(v___x_908_, 2, v___x_907_);
v___x_909_ = lean_box(0);
v___x_910_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_903_, v___x_908_, v___x_909_, v___x_906_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
lean_dec_ref_known(v___x_908_, 3);
lean_dec(v_a_903_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_927_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_927_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_927_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_927_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_snd_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_925_; 
v_snd_915_ = lean_ctor_get(v_a_911_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v_a_911_);
if (v_isSharedCheck_925_ == 0)
{
lean_object* v_unused_926_; 
v_unused_926_ = lean_ctor_get(v_a_911_, 0);
lean_dec(v_unused_926_);
v___x_917_ = v_a_911_;
v_isShared_918_ = v_isSharedCheck_925_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_snd_915_);
lean_dec(v_a_911_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_925_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_909_);
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_snd_915_);
v___x_920_ = v_reuseFailAlloc_924_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_922_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_920_);
v___x_922_ = v___x_913_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
else
{
return v___x_910_;
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec_ref(v_a_890_);
v_a_928_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_902_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_902_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go___boxed(lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec(v_a_937_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(lean_object* v_a_949_, lean_object* v_range_950_, lean_object* v_b_951_, lean_object* v_i_952_, lean_object* v_hs_953_, lean_object* v_hl_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_949_, v_range_950_, v_b_951_, v_i_952_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___boxed(lean_object** _args){
lean_object* v_a_968_ = _args[0];
lean_object* v_range_969_ = _args[1];
lean_object* v_b_970_ = _args[2];
lean_object* v_i_971_ = _args[3];
lean_object* v_hs_972_ = _args[4];
lean_object* v_hl_973_ = _args[5];
lean_object* v___y_974_ = _args[6];
lean_object* v___y_975_ = _args[7];
lean_object* v___y_976_ = _args[8];
lean_object* v___y_977_ = _args[9];
lean_object* v___y_978_ = _args[10];
lean_object* v___y_979_ = _args[11];
lean_object* v___y_980_ = _args[12];
lean_object* v___y_981_ = _args[13];
lean_object* v___y_982_ = _args[14];
lean_object* v___y_983_ = _args[15];
lean_object* v___y_984_ = _args[16];
lean_object* v___y_985_ = _args[17];
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(v_a_968_, v_range_969_, v_b_970_, v_i_971_, v_hs_972_, v_hl_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v_range_969_);
lean_dec_ref(v_a_968_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(lean_object* v_as_987_, size_t v_sz_988_, size_t v_i_989_, lean_object* v_b_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_987_, v_sz_988_, v_i_989_, v_b_990_, v___y_991_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1004_, lean_object* v_sz_1005_, lean_object* v_i_1006_, lean_object* v_b_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
size_t v_sz_boxed_1020_; size_t v_i_boxed_1021_; lean_object* v_res_1022_; 
v_sz_boxed_1020_ = lean_unbox_usize(v_sz_1005_);
lean_dec(v_sz_1005_);
v_i_boxed_1021_ = lean_unbox_usize(v_i_1006_);
lean_dec(v_i_1006_);
v_res_1022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(v_as_1004_, v_sz_boxed_1020_, v_i_boxed_1021_, v_b_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v_as_1004_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(lean_object* v_as_1023_, size_t v_sz_1024_, size_t v_i_1025_, lean_object* v_b_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1023_, v_sz_1024_, v_i_1025_, v_b_1026_, v___y_1027_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_as_1040_, lean_object* v_sz_1041_, lean_object* v_i_1042_, lean_object* v_b_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
size_t v_sz_boxed_1056_; size_t v_i_boxed_1057_; lean_object* v_res_1058_; 
v_sz_boxed_1056_ = lean_unbox_usize(v_sz_1041_);
lean_dec(v_sz_1041_);
v_i_boxed_1057_ = lean_unbox_usize(v_i_1042_);
lean_dec(v_i_1042_);
v_res_1058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(v_as_1040_, v_sz_boxed_1056_, v_i_boxed_1057_, v_b_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v_as_1040_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1059_, v_a_1067_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v_vars_1072_; lean_object* v_size_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v_vars_1072_ = lean_ctor_get(v_a_1071_, 0);
lean_inc_ref(v_vars_1072_);
lean_dec(v_a_1071_);
v_size_1073_ = lean_ctor_get(v_vars_1072_, 2);
lean_inc(v_size_1073_);
lean_dec_ref(v_vars_1072_);
v___x_1074_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0));
v___x_1075_ = lean_mk_array(v_size_1073_, v___x_1074_);
v___x_1076_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v___x_1075_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1085_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v_snd_1081_; lean_object* v___x_1083_; 
v_snd_1081_ = lean_ctor_get(v_a_1077_, 1);
lean_inc(v_snd_1081_);
lean_dec(v_a_1077_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v_snd_1081_);
v___x_1083_ = v___x_1079_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_snd_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_a_1086_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1076_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1076_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
v_a_1094_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1070_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1070_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo___boxed(lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec(v_a_1102_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(lean_object* v_info_1114_){
_start:
{
lean_object* v_maxLowerCoeff_1115_; lean_object* v_maxUpperCoeff_1116_; lean_object* v_maxDvdCoeff_1117_; lean_object* v___y_1119_; uint8_t v___x_1121_; 
v_maxLowerCoeff_1115_ = lean_ctor_get(v_info_1114_, 0);
v_maxUpperCoeff_1116_ = lean_ctor_get(v_info_1114_, 1);
v_maxDvdCoeff_1117_ = lean_ctor_get(v_info_1114_, 2);
v___x_1121_ = lean_nat_dec_le(v_maxLowerCoeff_1115_, v_maxUpperCoeff_1116_);
if (v___x_1121_ == 0)
{
v___y_1119_ = v_maxUpperCoeff_1116_;
goto v___jp_1118_;
}
else
{
v___y_1119_ = v_maxLowerCoeff_1115_;
goto v___jp_1118_;
}
v___jp_1118_:
{
uint8_t v___x_1120_; 
v___x_1120_ = lean_nat_dec_le(v_maxDvdCoeff_1117_, v___y_1119_);
if (v___x_1120_ == 0)
{
lean_inc(v_maxDvdCoeff_1117_);
return v_maxDvdCoeff_1117_;
}
else
{
lean_inc(v___y_1119_);
return v___y_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081___boxed(lean_object* v_info_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v_info_1122_);
lean_dec_ref(v_info_1122_);
return v_res_1123_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(lean_object* v_infos_1124_, lean_object* v_x_1125_, lean_object* v_y_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1127_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1128_ = lean_array_get_borrowed(v___x_1127_, v_infos_1124_, v_x_1125_);
v___x_1129_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1128_);
v___x_1130_ = lean_array_get_borrowed(v___x_1127_, v_infos_1124_, v_y_1126_);
v___x_1131_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1130_);
v___x_1132_ = lean_nat_dec_lt(v___x_1129_, v___x_1131_);
if (v___x_1132_ == 0)
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_nat_dec_eq(v___x_1129_, v___x_1131_);
lean_dec(v___x_1131_);
lean_dec(v___x_1129_);
if (v___x_1133_ == 0)
{
uint8_t v___x_1134_; 
v___x_1134_ = 0;
return v___x_1134_;
}
else
{
uint8_t v___x_1135_; 
v___x_1135_ = 1;
return v___x_1135_;
}
}
else
{
uint8_t v___x_1136_; 
lean_dec(v___x_1131_);
lean_dec(v___x_1129_);
v___x_1136_ = 2;
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081___boxed(lean_object* v_infos_1137_, lean_object* v_x_1138_, lean_object* v_y_1139_){
_start:
{
uint8_t v_res_1140_; lean_object* v_r_1141_; 
v_res_1140_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1137_, v_x_1138_, v_y_1139_);
lean_dec(v_y_1139_);
lean_dec(v_x_1138_);
lean_dec_ref(v_infos_1137_);
v_r_1141_ = lean_box(v_res_1140_);
return v_r_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(lean_object* v_info_1142_){
_start:
{
lean_object* v_maxLowerCoeff_1143_; lean_object* v_maxUpperCoeff_1144_; lean_object* v_maxDvdCoeff_1145_; lean_object* v___y_1147_; uint8_t v___x_1149_; 
v_maxLowerCoeff_1143_ = lean_ctor_get(v_info_1142_, 0);
v_maxUpperCoeff_1144_ = lean_ctor_get(v_info_1142_, 1);
v_maxDvdCoeff_1145_ = lean_ctor_get(v_info_1142_, 2);
v___x_1149_ = lean_nat_dec_le(v_maxLowerCoeff_1143_, v_maxUpperCoeff_1144_);
if (v___x_1149_ == 0)
{
v___y_1147_ = v_maxLowerCoeff_1143_;
goto v___jp_1146_;
}
else
{
v___y_1147_ = v_maxUpperCoeff_1144_;
goto v___jp_1146_;
}
v___jp_1146_:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_nat_dec_le(v_maxDvdCoeff_1145_, v___y_1147_);
if (v___x_1148_ == 0)
{
lean_inc(v_maxDvdCoeff_1145_);
return v_maxDvdCoeff_1145_;
}
else
{
lean_inc(v___y_1147_);
return v___y_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082___boxed(lean_object* v_info_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v_info_1150_);
lean_dec_ref(v_info_1150_);
return v_res_1151_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(lean_object* v_infos_1152_, lean_object* v_x_1153_, lean_object* v_y_1154_){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1155_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1156_ = lean_array_get_borrowed(v___x_1155_, v_infos_1152_, v_x_1153_);
v___x_1157_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1156_);
v___x_1158_ = lean_array_get_borrowed(v___x_1155_, v_infos_1152_, v_y_1154_);
v___x_1159_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1158_);
v___x_1160_ = lean_nat_dec_lt(v___x_1157_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_nat_dec_eq(v___x_1157_, v___x_1159_);
lean_dec(v___x_1159_);
lean_dec(v___x_1157_);
if (v___x_1161_ == 0)
{
uint8_t v___x_1162_; 
v___x_1162_ = 0;
return v___x_1162_;
}
else
{
uint8_t v___x_1163_; 
v___x_1163_ = 1;
return v___x_1163_;
}
}
else
{
uint8_t v___x_1164_; 
lean_dec(v___x_1159_);
lean_dec(v___x_1157_);
v___x_1164_ = 2;
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082___boxed(lean_object* v_infos_1165_, lean_object* v_x_1166_, lean_object* v_y_1167_){
_start:
{
uint8_t v_res_1168_; lean_object* v_r_1169_; 
v_res_1168_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1165_, v_x_1166_, v_y_1167_);
lean_dec(v_y_1167_);
lean_dec(v_x_1166_);
lean_dec_ref(v_infos_1165_);
v_r_1169_ = lean_box(v_res_1168_);
return v_r_1169_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(lean_object* v_infos_1170_, lean_object* v_x_1171_, lean_object* v_y_1172_){
_start:
{
uint8_t v___y_1174_; uint8_t v___x_1179_; 
v___x_1179_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1170_, v_x_1171_, v_y_1172_);
if (v___x_1179_ == 1)
{
uint8_t v___x_1180_; 
v___x_1180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1170_, v_x_1171_, v_y_1172_);
v___y_1174_ = v___x_1180_;
goto v___jp_1173_;
}
else
{
v___y_1174_ = v___x_1179_;
goto v___jp_1173_;
}
v___jp_1173_:
{
if (v___y_1174_ == 1)
{
uint8_t v___x_1175_; 
v___x_1175_ = lean_nat_dec_lt(v_x_1171_, v_y_1172_);
if (v___x_1175_ == 0)
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_nat_dec_eq(v_x_1171_, v_y_1172_);
if (v___x_1176_ == 0)
{
uint8_t v___x_1177_; 
v___x_1177_ = 2;
return v___x_1177_;
}
else
{
return v___y_1174_;
}
}
else
{
uint8_t v___x_1178_; 
v___x_1178_ = 0;
return v___x_1178_;
}
}
else
{
return v___y_1174_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp___boxed(lean_object* v_infos_1181_, lean_object* v_x_1182_, lean_object* v_y_1183_){
_start:
{
uint8_t v_res_1184_; lean_object* v_r_1185_; 
v_res_1184_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1181_, v_x_1182_, v_y_1183_);
lean_dec(v_y_1183_);
lean_dec(v_x_1182_);
lean_dec_ref(v_infos_1181_);
v_r_1185_ = lean_box(v_res_1184_);
return v_r_1185_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(lean_object* v_infos_1186_, lean_object* v_x_1187_, lean_object* v_y_1188_){
_start:
{
uint8_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1189_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1186_, v_x_1187_, v_y_1188_);
v___x_1190_ = lean_box(v___x_1189_);
v___x_1191_ = lean_obj_tag_nat(v___x_1190_);
lean_dec(v___x_1190_);
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = lean_nat_dec_eq(v___x_1191_, v___x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0___boxed(lean_object* v_infos_1194_, lean_object* v_x_1195_, lean_object* v_y_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1194_, v_x_1195_, v_y_1196_);
lean_dec(v_y_1196_);
lean_dec(v_x_1195_);
lean_dec_ref(v_infos_1194_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(lean_object* v_infos_1199_, lean_object* v_hi_1200_, lean_object* v_pivot_1201_, lean_object* v_as_1202_, lean_object* v_i_1203_, lean_object* v_k_1204_){
_start:
{
uint8_t v___x_1205_; 
v___x_1205_ = lean_nat_dec_lt(v_k_1204_, v_hi_1200_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_dec(v_k_1204_);
v___x_1206_ = lean_array_fswap(v_as_1202_, v_i_1203_, v_hi_1200_);
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_i_1203_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
return v___x_1207_;
}
else
{
lean_object* v___x_1208_; uint8_t v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1208_ = lean_array_fget_borrowed(v_as_1202_, v_k_1204_);
v___x_1209_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1199_, v___x_1208_, v_pivot_1201_);
v___x_1210_ = lean_box(v___x_1209_);
v___x_1211_ = lean_obj_tag_nat(v___x_1210_);
lean_dec(v___x_1210_);
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = lean_nat_dec_eq(v___x_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_unsigned_to_nat(1u);
v___x_1215_ = lean_nat_add(v_k_1204_, v___x_1214_);
lean_dec(v_k_1204_);
v_k_1204_ = v___x_1215_;
goto _start;
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1217_ = lean_array_fswap(v_as_1202_, v_i_1203_, v_k_1204_);
v___x_1218_ = lean_unsigned_to_nat(1u);
v___x_1219_ = lean_nat_add(v_i_1203_, v___x_1218_);
lean_dec(v_i_1203_);
v___x_1220_ = lean_nat_add(v_k_1204_, v___x_1218_);
lean_dec(v_k_1204_);
v_as_1202_ = v___x_1217_;
v_i_1203_ = v___x_1219_;
v_k_1204_ = v___x_1220_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg___boxed(lean_object* v_infos_1222_, lean_object* v_hi_1223_, lean_object* v_pivot_1224_, lean_object* v_as_1225_, lean_object* v_i_1226_, lean_object* v_k_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_infos_1222_, v_hi_1223_, v_pivot_1224_, v_as_1225_, v_i_1226_, v_k_1227_);
lean_dec(v_pivot_1224_);
lean_dec(v_hi_1223_);
lean_dec_ref(v_infos_1222_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(lean_object* v_infos_1229_, lean_object* v_n_1230_, lean_object* v_as_1231_, lean_object* v_lo_1232_, lean_object* v_hi_1233_){
_start:
{
lean_object* v___y_1235_; uint8_t v___x_1245_; 
v___x_1245_ = lean_nat_dec_lt(v_lo_1232_, v_hi_1233_);
if (v___x_1245_ == 0)
{
lean_dec(v_lo_1232_);
return v_as_1231_;
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v_mid_1248_; lean_object* v___y_1250_; lean_object* v___y_1256_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1246_ = lean_nat_add(v_lo_1232_, v_hi_1233_);
v___x_1247_ = lean_unsigned_to_nat(1u);
v_mid_1248_ = lean_nat_shiftr(v___x_1246_, v___x_1247_);
lean_dec(v___x_1246_);
v___x_1261_ = lean_array_fget_borrowed(v_as_1231_, v_mid_1248_);
v___x_1262_ = lean_array_fget_borrowed(v_as_1231_, v_lo_1232_);
v___x_1263_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1229_, v___x_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
v___y_1256_ = v_as_1231_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_array_fswap(v_as_1231_, v_lo_1232_, v_mid_1248_);
v___y_1256_ = v___x_1264_;
goto v___jp_1255_;
}
v___jp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1251_ = lean_array_fget_borrowed(v___y_1250_, v_mid_1248_);
v___x_1252_ = lean_array_fget_borrowed(v___y_1250_, v_hi_1233_);
v___x_1253_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1229_, v___x_1251_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_dec(v_mid_1248_);
v___y_1235_ = v___y_1250_;
goto v___jp_1234_;
}
else
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_array_fswap(v___y_1250_, v_mid_1248_, v_hi_1233_);
lean_dec(v_mid_1248_);
v___y_1235_ = v___x_1254_;
goto v___jp_1234_;
}
}
v___jp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1257_ = lean_array_fget_borrowed(v___y_1256_, v_hi_1233_);
v___x_1258_ = lean_array_fget_borrowed(v___y_1256_, v_lo_1232_);
v___x_1259_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1229_, v___x_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
v___y_1250_ = v___y_1256_;
goto v___jp_1249_;
}
else
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_array_fswap(v___y_1256_, v_lo_1232_, v_hi_1233_);
v___y_1250_ = v___x_1260_;
goto v___jp_1249_;
}
}
}
v___jp_1234_:
{
lean_object* v_pivot_1236_; lean_object* v___x_1237_; lean_object* v_fst_1238_; lean_object* v_snd_1239_; uint8_t v___x_1240_; 
v_pivot_1236_ = lean_array_fget(v___y_1235_, v_hi_1233_);
lean_inc_n(v_lo_1232_, 2);
v___x_1237_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_infos_1229_, v_hi_1233_, v_pivot_1236_, v___y_1235_, v_lo_1232_, v_lo_1232_);
lean_dec(v_pivot_1236_);
v_fst_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_fst_1238_);
v_snd_1239_ = lean_ctor_get(v___x_1237_, 1);
lean_inc(v_snd_1239_);
lean_dec_ref(v___x_1237_);
v___x_1240_ = lean_nat_dec_le(v_hi_1233_, v_fst_1238_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1229_, v_n_1230_, v_snd_1239_, v_lo_1232_, v_fst_1238_);
v___x_1242_ = lean_unsigned_to_nat(1u);
v___x_1243_ = lean_nat_add(v_fst_1238_, v___x_1242_);
lean_dec(v_fst_1238_);
v_as_1231_ = v___x_1241_;
v_lo_1232_ = v___x_1243_;
goto _start;
}
else
{
lean_dec(v_fst_1238_);
lean_dec(v_lo_1232_);
return v_snd_1239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___boxed(lean_object* v_infos_1265_, lean_object* v_n_1266_, lean_object* v_as_1267_, lean_object* v_lo_1268_, lean_object* v_hi_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1265_, v_n_1266_, v_as_1267_, v_lo_1268_, v_hi_1269_);
lean_dec(v_hi_1269_);
lean_dec(v_n_1266_);
lean_dec_ref(v_infos_1265_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(lean_object* v_infos_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1272_, v_a_1273_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1300_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1300_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1300_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_vars_1280_; lean_object* v_size_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_vars_1280_ = lean_ctor_get(v_a_1276_, 0);
lean_inc_ref(v_vars_1280_);
lean_dec(v_a_1276_);
v_size_1281_ = lean_ctor_get(v_vars_1280_, 2);
lean_inc(v_size_1281_);
lean_dec_ref(v_vars_1280_);
v___x_1282_ = l_Array_range(v_size_1281_);
v___x_1283_ = lean_array_get_size(v___x_1282_);
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = lean_nat_dec_eq(v___x_1283_, v___x_1291_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___y_1296_; uint8_t v___x_1298_; 
v___x_1293_ = lean_unsigned_to_nat(1u);
v___x_1294_ = lean_nat_sub(v___x_1283_, v___x_1293_);
v___x_1298_ = lean_nat_dec_le(v___x_1291_, v___x_1294_);
if (v___x_1298_ == 0)
{
lean_inc(v___x_1294_);
v___y_1296_ = v___x_1294_;
goto v___jp_1295_;
}
else
{
v___y_1296_ = v___x_1291_;
goto v___jp_1295_;
}
v___jp_1295_:
{
uint8_t v___x_1297_; 
v___x_1297_ = lean_nat_dec_le(v___y_1296_, v___x_1294_);
if (v___x_1297_ == 0)
{
lean_dec(v___x_1294_);
lean_inc(v___y_1296_);
v___y_1285_ = v___y_1296_;
v___y_1286_ = v___y_1296_;
goto v___jp_1284_;
}
else
{
v___y_1285_ = v___y_1296_;
v___y_1286_ = v___x_1294_;
goto v___jp_1284_;
}
}
}
else
{
lean_object* v___x_1299_; 
lean_del_object(v___x_1278_);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1282_);
return v___x_1299_;
}
v___jp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1271_, v___x_1283_, v___x_1282_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1287_);
v___x_1289_ = v___x_1278_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
v_a_1301_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1275_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1275_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg___boxed(lean_object* v_infos_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(v_infos_1309_, v_a_1310_, v_a_1311_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_infos_1309_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(lean_object* v_infos_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(v_infos_1314_, v_a_1315_, v_a_1323_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___boxed(lean_object* v_infos_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_infos_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_infos_1327_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(lean_object* v_infos_1340_, lean_object* v_n_1341_, lean_object* v_as_1342_, lean_object* v_lo_1343_, lean_object* v_hi_1344_, lean_object* v_w_1345_, lean_object* v_hlo_1346_, lean_object* v_hhi_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1340_, v_n_1341_, v_as_1342_, v_lo_1343_, v_hi_1344_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___boxed(lean_object* v_infos_1349_, lean_object* v_n_1350_, lean_object* v_as_1351_, lean_object* v_lo_1352_, lean_object* v_hi_1353_, lean_object* v_w_1354_, lean_object* v_hlo_1355_, lean_object* v_hhi_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(v_infos_1349_, v_n_1350_, v_as_1351_, v_lo_1352_, v_hi_1353_, v_w_1354_, v_hlo_1355_, v_hhi_1356_);
lean_dec(v_hi_1353_);
lean_dec(v_n_1350_);
lean_dec_ref(v_infos_1349_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(lean_object* v_infos_1358_, lean_object* v_n_1359_, lean_object* v_lo_1360_, lean_object* v_hi_1361_, lean_object* v_hhi_1362_, lean_object* v_pivot_1363_, lean_object* v_as_1364_, lean_object* v_i_1365_, lean_object* v_k_1366_, lean_object* v_ilo_1367_, lean_object* v_ik_1368_, lean_object* v_w_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_infos_1358_, v_hi_1361_, v_pivot_1363_, v_as_1364_, v_i_1365_, v_k_1366_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___boxed(lean_object* v_infos_1371_, lean_object* v_n_1372_, lean_object* v_lo_1373_, lean_object* v_hi_1374_, lean_object* v_hhi_1375_, lean_object* v_pivot_1376_, lean_object* v_as_1377_, lean_object* v_i_1378_, lean_object* v_k_1379_, lean_object* v_ilo_1380_, lean_object* v_ik_1381_, lean_object* v_w_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(v_infos_1371_, v_n_1372_, v_lo_1373_, v_hi_1374_, v_hhi_1375_, v_pivot_1376_, v_as_1377_, v_i_1378_, v_k_1379_, v_ilo_1380_, v_ik_1381_, v_w_1382_);
lean_dec(v_pivot_1376_);
lean_dec(v_hi_1374_);
lean_dec(v_lo_1373_);
lean_dec(v_n_1372_);
lean_dec_ref(v_infos_1371_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(lean_object* v_perm_1384_, lean_object* v_range_1385_, lean_object* v_b_1386_, lean_object* v_i_1387_){
_start:
{
lean_object* v_stop_1388_; lean_object* v_step_1389_; uint8_t v___x_1390_; 
v_stop_1388_ = lean_ctor_get(v_range_1385_, 1);
v_step_1389_ = lean_ctor_get(v_range_1385_, 2);
v___x_1390_ = lean_nat_dec_lt(v_i_1387_, v_stop_1388_);
if (v___x_1390_ == 0)
{
lean_dec(v_i_1387_);
return v_b_1386_;
}
else
{
lean_object* v___x_1391_; lean_object* v_inv_1392_; lean_object* v___x_1393_; 
v___x_1391_ = lean_array_fget_borrowed(v_perm_1384_, v_i_1387_);
lean_inc(v_i_1387_);
v_inv_1392_ = lean_array_set(v_b_1386_, v___x_1391_, v_i_1387_);
v___x_1393_ = lean_nat_add(v_i_1387_, v_step_1389_);
lean_dec(v_i_1387_);
v_b_1386_ = v_inv_1392_;
v_i_1387_ = v___x_1393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg___boxed(lean_object* v_perm_1395_, lean_object* v_range_1396_, lean_object* v_b_1397_, lean_object* v_i_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1395_, v_range_1396_, v_b_1397_, v_i_1398_);
lean_dec_ref(v_range_1396_);
lean_dec_ref(v_perm_1395_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(lean_object* v_perm_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v_inv_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1401_ = lean_array_get_size(v_perm_1400_);
v___x_1402_ = lean_unsigned_to_nat(0u);
v_inv_1403_ = lean_mk_array(v___x_1401_, v___x_1402_);
v___x_1404_ = lean_unsigned_to_nat(1u);
v___x_1405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1402_);
lean_ctor_set(v___x_1405_, 1, v___x_1401_);
lean_ctor_set(v___x_1405_, 2, v___x_1404_);
v___x_1406_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1400_, v___x_1405_, v_inv_1403_, v___x_1402_);
lean_dec_ref_known(v___x_1405_, 3);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv___boxed(lean_object* v_perm_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_perm_1407_);
lean_dec_ref(v_perm_1407_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(lean_object* v_perm_1409_, lean_object* v_range_1410_, lean_object* v_b_1411_, lean_object* v_i_1412_, lean_object* v_hs_1413_, lean_object* v_hl_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1409_, v_range_1410_, v_b_1411_, v_i_1412_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___boxed(lean_object* v_perm_1416_, lean_object* v_range_1417_, lean_object* v_b_1418_, lean_object* v_i_1419_, lean_object* v_hs_1420_, lean_object* v_hl_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(v_perm_1416_, v_range_1417_, v_b_1418_, v_i_1419_, v_hs_1420_, v_hl_1421_);
lean_dec_ref(v_range_1417_);
lean_dec_ref(v_perm_1416_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_reorder(lean_object* v_p_1423_, lean_object* v_old2new_1424_){
_start:
{
if (lean_obj_tag(v_p_1423_) == 0)
{
return v_p_1423_;
}
else
{
lean_object* v_k_1425_; lean_object* v_v_1426_; lean_object* v_p_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1437_; 
v_k_1425_ = lean_ctor_get(v_p_1423_, 0);
v_v_1426_ = lean_ctor_get(v_p_1423_, 1);
v_p_1427_ = lean_ctor_get(v_p_1423_, 2);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_p_1423_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1429_ = v_p_1423_;
v_isShared_1430_ = v_isSharedCheck_1437_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_p_1427_);
lean_inc(v_v_1426_);
lean_inc(v_k_1425_);
lean_dec(v_p_1423_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1437_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = lean_array_get_borrowed(v___x_1431_, v_old2new_1424_, v_v_1426_);
lean_dec(v_v_1426_);
v___x_1433_ = l_Int_Internal_Linear_Poly_reorder(v_p_1427_, v_old2new_1424_);
lean_inc(v___x_1432_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 2, v___x_1433_);
lean_ctor_set(v___x_1429_, 1, v___x_1432_);
v___x_1435_ = v___x_1429_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_reorder___boxed(lean_object* v_p_1438_, lean_object* v_old2new_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Int_Internal_Linear_Poly_reorder(v_p_1438_, v_old2new_1439_);
lean_dec_ref(v_old2new_1439_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(lean_object* v_c_1441_, lean_object* v_old2new_1442_){
_start:
{
lean_object* v_d_1443_; lean_object* v_p_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_d_1443_ = lean_ctor_get(v_c_1441_, 0);
lean_inc(v_d_1443_);
v_p_1444_ = lean_ctor_get(v_c_1441_, 1);
lean_inc_ref(v_p_1444_);
v___x_1445_ = l_Int_Internal_Linear_Poly_reorder(v_p_1444_, v_old2new_1442_);
v___x_1446_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_c_1441_);
v___x_1447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1447_, 0, v_d_1443_);
lean_ctor_set(v___x_1447_, 1, v___x_1445_);
lean_ctor_set(v___x_1447_, 2, v___x_1446_);
v___x_1448_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder___boxed(lean_object* v_c_1449_, lean_object* v_old2new_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_c_1449_, v_old2new_1450_);
lean_dec_ref(v_old2new_1450_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(lean_object* v_c_1452_, lean_object* v_old2new_1453_){
_start:
{
lean_object* v_p_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v_p_1454_ = lean_ctor_get(v_c_1452_, 0);
lean_inc_ref(v_p_1454_);
v___x_1455_ = l_Int_Internal_Linear_Poly_reorder(v_p_1454_, v_old2new_1453_);
v___x_1456_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_c_1452_);
v___x_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(v___x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder___boxed(lean_object* v_c_1459_, lean_object* v_old2new_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_c_1459_, v_old2new_1460_);
lean_dec_ref(v_old2new_1460_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(lean_object* v_c_1462_, lean_object* v_old2new_1463_){
_start:
{
lean_object* v_p_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_p_1464_ = lean_ctor_get(v_c_1462_, 0);
lean_inc_ref(v_p_1464_);
v___x_1465_ = l_Int_Internal_Linear_Poly_reorder(v_p_1464_, v_old2new_1463_);
v___x_1466_ = lean_alloc_ctor(16, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_c_1462_);
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1465_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v___x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder___boxed(lean_object* v_c_1469_, lean_object* v_old2new_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_c_1469_, v_old2new_1470_);
lean_dec_ref(v_old2new_1470_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(lean_object* v_c_1472_, lean_object* v_old2new_1473_){
_start:
{
lean_object* v_p_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_p_1474_ = lean_ctor_get(v_c_1472_, 0);
lean_inc_ref(v_p_1474_);
v___x_1475_ = l_Int_Internal_Linear_Poly_reorder(v_p_1474_, v_old2new_1473_);
v___x_1476_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1476_, 0, v_c_1472_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(v___x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder___boxed(lean_object* v_c_1479_, lean_object* v_old2new_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_c_1479_, v_old2new_1480_);
lean_dec_ref(v_old2new_1480_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(lean_object* v_new2old_1482_, lean_object* v_inst_1483_, lean_object* v_m_1484_, lean_object* v_i_1485_, lean_object* v_h_1486_, lean_object* v_____s_1487_){
_start:
{
lean_object* v_j_1488_; lean_object* v___x_1489_; lean_object* v_r_1490_; lean_object* v___x_1491_; 
v_j_1488_ = lean_array_fget_borrowed(v_new2old_1482_, v_i_1485_);
v___x_1489_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_1483_, v_m_1484_, v_j_1488_);
v_r_1490_ = l_Lean_PersistentArray_push___redArg(v_____s_1487_, v___x_1489_);
v___x_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_r_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed(lean_object* v_new2old_1492_, lean_object* v_inst_1493_, lean_object* v_m_1494_, lean_object* v_i_1495_, lean_object* v_h_1496_, lean_object* v_____s_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(v_new2old_1492_, v_inst_1493_, v_m_1494_, v_i_1495_, v_h_1496_, v_____s_1497_);
lean_dec(v_i_1495_);
lean_dec_ref(v_m_1494_);
lean_dec(v_inst_1493_);
lean_dec_ref(v_new2old_1492_);
return v_res_1498_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = lean_unsigned_to_nat(32u);
v___x_1519_ = lean_mk_empty_array_with_capacity(v___x_1518_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11(void){
_start:
{
size_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v_r_1526_; 
v___x_1521_ = ((size_t)5ULL);
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = lean_unsigned_to_nat(32u);
v___x_1524_ = lean_mk_empty_array_with_capacity(v___x_1523_);
v___x_1525_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10);
v_r_1526_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_r_1526_, 0, v___x_1525_);
lean_ctor_set(v_r_1526_, 1, v___x_1524_);
lean_ctor_set(v_r_1526_, 2, v___x_1522_);
lean_ctor_set(v_r_1526_, 3, v___x_1522_);
lean_ctor_set_usize(v_r_1526_, 4, v___x_1521_);
return v_r_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(lean_object* v_inst_1527_, lean_object* v_m_1528_, lean_object* v_new2old_1529_){
_start:
{
lean_object* v___f_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v_r_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_inc_ref(v_new2old_1529_);
v___f_1530_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1530_, 0, v_new2old_1529_);
lean_closure_set(v___f_1530_, 1, v_inst_1527_);
lean_closure_set(v___f_1530_, 2, v_m_1528_);
v___x_1531_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9));
v___x_1532_ = lean_unsigned_to_nat(0u);
v_r_1533_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11);
v___x_1534_ = lean_array_get_size(v_new2old_1529_);
lean_dec_ref(v_new2old_1529_);
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1532_);
lean_ctor_set(v___x_1536_, 1, v___x_1534_);
lean_ctor_set(v___x_1536_, 2, v___x_1535_);
v___x_1537_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), v___x_1531_, v___x_1536_, v___f_1530_, v_r_1533_, v___x_1532_, lean_box(0), lean_box(0));
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap(lean_object* v_00_u03b1_1538_, lean_object* v_inst_1539_, lean_object* v_m_1540_, lean_object* v_new2old_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v_inst_1539_, v_m_1540_, v_new2old_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_){
_start:
{
lean_object* v_ks_1547_; lean_object* v_vs_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1572_; 
v_ks_1547_ = lean_ctor_get(v_x_1543_, 0);
v_vs_1548_ = lean_ctor_get(v_x_1543_, 1);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_x_1543_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1550_ = v_x_1543_;
v_isShared_1551_ = v_isSharedCheck_1572_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_vs_1548_);
lean_inc(v_ks_1547_);
lean_dec(v_x_1543_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1572_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = lean_array_get_size(v_ks_1547_);
v___x_1553_ = lean_nat_dec_lt(v_x_1544_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
lean_dec(v_x_1544_);
v___x_1554_ = lean_array_push(v_ks_1547_, v_x_1545_);
v___x_1555_ = lean_array_push(v_vs_1548_, v_x_1546_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 1, v___x_1555_);
lean_ctor_set(v___x_1550_, 0, v___x_1554_);
v___x_1557_ = v___x_1550_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
else
{
lean_object* v_k_x27_1559_; uint8_t v___x_1560_; 
v_k_x27_1559_ = lean_array_fget_borrowed(v_ks_1547_, v_x_1544_);
v___x_1560_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_1545_, v_k_x27_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1562_; 
if (v_isShared_1551_ == 0)
{
v___x_1562_ = v___x_1550_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_ks_1547_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_vs_1548_);
v___x_1562_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = lean_unsigned_to_nat(1u);
v___x_1564_ = lean_nat_add(v_x_1544_, v___x_1563_);
lean_dec(v_x_1544_);
v_x_1543_ = v___x_1562_;
v_x_1544_ = v___x_1564_;
goto _start;
}
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1567_ = lean_array_fset(v_ks_1547_, v_x_1544_, v_x_1545_);
v___x_1568_ = lean_array_fset(v_vs_1548_, v_x_1544_, v_x_1546_);
lean_dec(v_x_1544_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 1, v___x_1568_);
lean_ctor_set(v___x_1550_, 0, v___x_1567_);
v___x_1570_ = v___x_1550_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1573_, lean_object* v_k_1574_, lean_object* v_v_1575_){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_unsigned_to_nat(0u);
v___x_1577_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1573_, v___x_1576_, v_k_1574_, v_v_1575_);
return v___x_1577_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(lean_object* v_x_1579_, size_t v_x_1580_, size_t v_x_1581_, lean_object* v_x_1582_, lean_object* v_x_1583_){
_start:
{
if (lean_obj_tag(v_x_1579_) == 0)
{
lean_object* v_es_1584_; size_t v___x_1585_; size_t v___x_1586_; lean_object* v_j_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v_es_1584_ = lean_ctor_get(v_x_1579_, 0);
v___x_1585_ = ((size_t)31ULL);
v___x_1586_ = lean_usize_land(v_x_1580_, v___x_1585_);
v_j_1587_ = lean_usize_to_nat(v___x_1586_);
v___x_1588_ = lean_array_get_size(v_es_1584_);
v___x_1589_ = lean_nat_dec_lt(v_j_1587_, v___x_1588_);
if (v___x_1589_ == 0)
{
lean_dec(v_j_1587_);
lean_dec(v_x_1583_);
lean_dec_ref(v_x_1582_);
return v_x_1579_;
}
else
{
lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1628_; 
lean_inc_ref(v_es_1584_);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_x_1579_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; 
v_unused_1629_ = lean_ctor_get(v_x_1579_, 0);
lean_dec(v_unused_1629_);
v___x_1591_ = v_x_1579_;
v_isShared_1592_ = v_isSharedCheck_1628_;
goto v_resetjp_1590_;
}
else
{
lean_dec(v_x_1579_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1628_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v_v_1593_; lean_object* v___x_1594_; lean_object* v_xs_x27_1595_; lean_object* v___y_1597_; 
v_v_1593_ = lean_array_fget(v_es_1584_, v_j_1587_);
v___x_1594_ = lean_box(0);
v_xs_x27_1595_ = lean_array_fset(v_es_1584_, v_j_1587_, v___x_1594_);
switch(lean_obj_tag(v_v_1593_))
{
case 0:
{
lean_object* v_key_1602_; lean_object* v_val_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1613_; 
v_key_1602_ = lean_ctor_get(v_v_1593_, 0);
v_val_1603_ = lean_ctor_get(v_v_1593_, 1);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_v_1593_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1605_ = v_v_1593_;
v_isShared_1606_ = v_isSharedCheck_1613_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_val_1603_);
lean_inc(v_key_1602_);
lean_dec(v_v_1593_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1613_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
uint8_t v___x_1607_; 
v___x_1607_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_1582_, v_key_1602_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_del_object(v___x_1605_);
v___x_1608_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1602_, v_val_1603_, v_x_1582_, v_x_1583_);
v___x_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
v___y_1597_ = v___x_1609_;
goto v___jp_1596_;
}
else
{
lean_object* v___x_1611_; 
lean_dec(v_val_1603_);
lean_dec(v_key_1602_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 1, v_x_1583_);
lean_ctor_set(v___x_1605_, 0, v_x_1582_);
v___x_1611_ = v___x_1605_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_x_1582_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_x_1583_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
v___y_1597_ = v___x_1611_;
goto v___jp_1596_;
}
}
}
}
case 1:
{
lean_object* v_node_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1626_; 
v_node_1614_ = lean_ctor_get(v_v_1593_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_v_1593_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1616_ = v_v_1593_;
v_isShared_1617_ = v_isSharedCheck_1626_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_node_1614_);
lean_dec(v_v_1593_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1626_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
size_t v___x_1618_; size_t v___x_1619_; size_t v___x_1620_; size_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1618_ = ((size_t)5ULL);
v___x_1619_ = lean_usize_shift_right(v_x_1580_, v___x_1618_);
v___x_1620_ = ((size_t)1ULL);
v___x_1621_ = lean_usize_add(v_x_1581_, v___x_1620_);
v___x_1622_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_node_1614_, v___x_1619_, v___x_1621_, v_x_1582_, v_x_1583_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1622_);
v___x_1624_ = v___x_1616_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
v___y_1597_ = v___x_1624_;
goto v___jp_1596_;
}
}
}
default: 
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v_x_1582_);
lean_ctor_set(v___x_1627_, 1, v_x_1583_);
v___y_1597_ = v___x_1627_;
goto v___jp_1596_;
}
}
v___jp_1596_:
{
lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1598_ = lean_array_fset(v_xs_x27_1595_, v_j_1587_, v___y_1597_);
lean_dec(v_j_1587_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1598_);
v___x_1600_ = v___x_1591_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
else
{
lean_object* v_ks_1630_; lean_object* v_vs_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1649_; 
v_ks_1630_ = lean_ctor_get(v_x_1579_, 0);
v_vs_1631_ = lean_ctor_get(v_x_1579_, 1);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_x_1579_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1633_ = v_x_1579_;
v_isShared_1634_ = v_isSharedCheck_1649_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_vs_1631_);
lean_inc(v_ks_1630_);
lean_dec(v_x_1579_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1649_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_ks_1630_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_vs_1631_);
v___x_1636_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v_newNode_1637_; size_t v___x_1638_; uint8_t v___x_1639_; 
v_newNode_1637_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v___x_1636_, v_x_1582_, v_x_1583_);
v___x_1638_ = ((size_t)7ULL);
v___x_1639_ = lean_usize_dec_le(v___x_1638_, v_x_1581_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1640_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1637_);
v___x_1641_ = lean_unsigned_to_nat(4u);
v___x_1642_ = lean_nat_dec_lt(v___x_1640_, v___x_1641_);
lean_dec(v___x_1640_);
if (v___x_1642_ == 0)
{
lean_object* v_ks_1643_; lean_object* v_vs_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v_ks_1643_ = lean_ctor_get(v_newNode_1637_, 0);
lean_inc_ref(v_ks_1643_);
v_vs_1644_ = lean_ctor_get(v_newNode_1637_, 1);
lean_inc_ref(v_vs_1644_);
lean_dec_ref(v_newNode_1637_);
v___x_1645_ = lean_unsigned_to_nat(0u);
v___x_1646_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0);
v___x_1647_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_x_1581_, v_ks_1643_, v_vs_1644_, v___x_1645_, v___x_1646_);
lean_dec_ref(v_vs_1644_);
lean_dec_ref(v_ks_1643_);
return v___x_1647_;
}
else
{
return v_newNode_1637_;
}
}
else
{
return v_newNode_1637_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(size_t v_depth_1650_, lean_object* v_keys_1651_, lean_object* v_vals_1652_, lean_object* v_i_1653_, lean_object* v_entries_1654_){
_start:
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = lean_array_get_size(v_keys_1651_);
v___x_1656_ = lean_nat_dec_lt(v_i_1653_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_dec(v_i_1653_);
return v_entries_1654_;
}
else
{
lean_object* v_k_1657_; lean_object* v_v_1658_; uint64_t v___x_1659_; size_t v_h_1660_; size_t v___x_1661_; lean_object* v___x_1662_; size_t v___x_1663_; size_t v___x_1664_; size_t v___x_1665_; size_t v_h_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_k_1657_ = lean_array_fget_borrowed(v_keys_1651_, v_i_1653_);
v_v_1658_ = lean_array_fget_borrowed(v_vals_1652_, v_i_1653_);
v___x_1659_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_k_1657_);
v_h_1660_ = lean_uint64_to_usize(v___x_1659_);
v___x_1661_ = ((size_t)5ULL);
v___x_1662_ = lean_unsigned_to_nat(1u);
v___x_1663_ = ((size_t)1ULL);
v___x_1664_ = lean_usize_sub(v_depth_1650_, v___x_1663_);
v___x_1665_ = lean_usize_mul(v___x_1661_, v___x_1664_);
v_h_1666_ = lean_usize_shift_right(v_h_1660_, v___x_1665_);
v___x_1667_ = lean_nat_add(v_i_1653_, v___x_1662_);
lean_dec(v_i_1653_);
lean_inc(v_v_1658_);
lean_inc(v_k_1657_);
v___x_1668_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_entries_1654_, v_h_1666_, v_depth_1650_, v_k_1657_, v_v_1658_);
v_i_1653_ = v___x_1667_;
v_entries_1654_ = v___x_1668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1670_, lean_object* v_keys_1671_, lean_object* v_vals_1672_, lean_object* v_i_1673_, lean_object* v_entries_1674_){
_start:
{
size_t v_depth_boxed_1675_; lean_object* v_res_1676_; 
v_depth_boxed_1675_ = lean_unbox_usize(v_depth_1670_);
lean_dec(v_depth_1670_);
v_res_1676_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1675_, v_keys_1671_, v_vals_1672_, v_i_1673_, v_entries_1674_);
lean_dec_ref(v_vals_1672_);
lean_dec_ref(v_keys_1671_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___boxed(lean_object* v_x_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_, lean_object* v_x_1681_){
_start:
{
size_t v_x_1760__boxed_1682_; size_t v_x_1761__boxed_1683_; lean_object* v_res_1684_; 
v_x_1760__boxed_1682_ = lean_unbox_usize(v_x_1678_);
lean_dec(v_x_1678_);
v_x_1761__boxed_1683_ = lean_unbox_usize(v_x_1679_);
lean_dec(v_x_1679_);
v_res_1684_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1677_, v_x_1760__boxed_1682_, v_x_1761__boxed_1683_, v_x_1680_, v_x_1681_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(lean_object* v_x_1685_, lean_object* v_x_1686_, lean_object* v_x_1687_){
_start:
{
uint64_t v___x_1688_; size_t v___x_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1688_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_1686_);
v___x_1689_ = lean_uint64_to_usize(v___x_1688_);
v___x_1690_ = ((size_t)1ULL);
v___x_1691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1685_, v___x_1689_, v___x_1690_, v_x_1686_, v_x_1687_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(lean_object* v_old2new_1692_, lean_object* v_x_1693_, lean_object* v_____s_1694_){
_start:
{
lean_object* v_fst_1695_; lean_object* v_snd_1696_; lean_object* v___x_1697_; lean_object* v_m_x27_1698_; lean_object* v___x_1699_; 
v_fst_1695_ = lean_ctor_get(v_x_1693_, 0);
lean_inc(v_fst_1695_);
v_snd_1696_ = lean_ctor_get(v_x_1693_, 1);
lean_inc(v_snd_1696_);
lean_dec_ref(v_x_1693_);
v___x_1697_ = l_Int_Internal_Linear_Poly_reorder(v_fst_1695_, v_old2new_1692_);
v_m_x27_1698_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_____s_1694_, v___x_1697_, v_snd_1696_);
v___x_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1699_, 0, v_m_x27_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed(lean_object* v_old2new_1700_, lean_object* v_x_1701_, lean_object* v_____s_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(v_old2new_1700_, v_x_1701_, v_____s_1702_);
lean_dec_ref(v_old2new_1700_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_f_1704_, lean_object* v_keys_1705_, lean_object* v_vals_1706_, lean_object* v_i_1707_, lean_object* v_acc_1708_){
_start:
{
lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1709_ = lean_array_get_size(v_keys_1705_);
v___x_1710_ = lean_nat_dec_lt(v_i_1707_, v___x_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_dec(v_i_1707_);
lean_dec_ref(v_f_1704_);
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_acc_1708_);
return v___x_1711_;
}
else
{
lean_object* v_k_1712_; lean_object* v_v_1713_; lean_object* v___x_1714_; 
v_k_1712_ = lean_array_fget_borrowed(v_keys_1705_, v_i_1707_);
v_v_1713_ = lean_array_fget_borrowed(v_vals_1706_, v_i_1707_);
lean_inc_ref(v_f_1704_);
lean_inc(v_v_1713_);
lean_inc(v_k_1712_);
v___x_1714_ = lean_apply_3(v_f_1704_, v_acc_1708_, v_k_1712_, v_v_1713_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_dec(v_i_1707_);
lean_dec_ref(v_f_1704_);
return v___x_1714_;
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_nat_add(v_i_1707_, v___x_1716_);
lean_dec(v_i_1707_);
v_i_1707_ = v___x_1717_;
v_acc_1708_ = v_a_1715_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_f_1719_, lean_object* v_keys_1720_, lean_object* v_vals_1721_, lean_object* v_i_1722_, lean_object* v_acc_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1719_, v_keys_1720_, v_vals_1721_, v_i_1722_, v_acc_1723_);
lean_dec_ref(v_vals_1721_);
lean_dec_ref(v_keys_1720_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_f_1725_, lean_object* v_as_1726_, size_t v_i_1727_, size_t v_stop_1728_, lean_object* v_b_1729_){
_start:
{
lean_object* v_a_1731_; lean_object* v___y_1736_; uint8_t v___x_1738_; 
v___x_1738_ = lean_usize_dec_eq(v_i_1727_, v_stop_1728_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_array_uget_borrowed(v_as_1726_, v_i_1727_);
switch(lean_obj_tag(v___x_1739_))
{
case 0:
{
lean_object* v_key_1740_; lean_object* v_val_1741_; lean_object* v___x_1742_; 
v_key_1740_ = lean_ctor_get(v___x_1739_, 0);
v_val_1741_ = lean_ctor_get(v___x_1739_, 1);
lean_inc_ref(v_f_1725_);
lean_inc(v_val_1741_);
lean_inc(v_key_1740_);
v___x_1742_ = lean_apply_3(v_f_1725_, v_b_1729_, v_key_1740_, v_val_1741_);
v___y_1736_ = v___x_1742_;
goto v___jp_1735_;
}
case 1:
{
lean_object* v_node_1743_; lean_object* v___x_1744_; 
v_node_1743_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_node_1743_);
lean_inc_ref(v_f_1725_);
v___x_1744_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1725_, v_node_1743_, v_b_1729_);
v___y_1736_ = v___x_1744_;
goto v___jp_1735_;
}
default: 
{
v_a_1731_ = v_b_1729_;
goto v___jp_1730_;
}
}
}
else
{
lean_object* v___x_1745_; 
lean_dec_ref(v_f_1725_);
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_b_1729_);
return v___x_1745_;
}
v___jp_1730_:
{
size_t v___x_1732_; size_t v___x_1733_; 
v___x_1732_ = ((size_t)1ULL);
v___x_1733_ = lean_usize_add(v_i_1727_, v___x_1732_);
v_i_1727_ = v___x_1733_;
v_b_1729_ = v_a_1731_;
goto _start;
}
v___jp_1735_:
{
if (lean_obj_tag(v___y_1736_) == 0)
{
lean_dec_ref(v_f_1725_);
return v___y_1736_;
}
else
{
lean_object* v_a_1737_; 
v_a_1737_ = lean_ctor_get(v___y_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___y_1736_, 1);
v_a_1731_ = v_a_1737_;
goto v___jp_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(lean_object* v_f_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_){
_start:
{
if (lean_obj_tag(v_x_1747_) == 0)
{
lean_object* v_es_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1762_; 
v_es_1749_ = lean_ctor_get(v_x_1747_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_x_1747_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1751_ = v_x_1747_;
v_isShared_1752_ = v_isSharedCheck_1762_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_es_1749_);
lean_dec(v_x_1747_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1762_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = lean_array_get_size(v_es_1749_);
v___x_1755_ = lean_nat_dec_lt(v___x_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref(v_es_1749_);
lean_dec_ref(v_f_1746_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set_tag(v___x_1751_, 1);
lean_ctor_set(v___x_1751_, 0, v_x_1748_);
v___x_1757_ = v___x_1751_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_x_1748_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
else
{
size_t v___x_1759_; size_t v___x_1760_; lean_object* v___x_1761_; 
lean_del_object(v___x_1751_);
v___x_1759_ = ((size_t)0ULL);
v___x_1760_ = lean_usize_of_nat(v___x_1754_);
v___x_1761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1746_, v_es_1749_, v___x_1759_, v___x_1760_, v_x_1748_);
lean_dec_ref(v_es_1749_);
return v___x_1761_;
}
}
}
else
{
lean_object* v_ks_1763_; lean_object* v_vs_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_ks_1763_ = lean_ctor_get(v_x_1747_, 0);
lean_inc_ref(v_ks_1763_);
v_vs_1764_ = lean_ctor_get(v_x_1747_, 1);
lean_inc_ref(v_vs_1764_);
lean_dec_ref_known(v_x_1747_, 2);
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1746_, v_ks_1763_, v_vs_1764_, v___x_1765_, v_x_1748_);
lean_dec_ref(v_vs_1764_);
lean_dec_ref(v_ks_1763_);
return v___x_1766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_f_1767_, lean_object* v_as_1768_, lean_object* v_i_1769_, lean_object* v_stop_1770_, lean_object* v_b_1771_){
_start:
{
size_t v_i_boxed_1772_; size_t v_stop_boxed_1773_; lean_object* v_res_1774_; 
v_i_boxed_1772_ = lean_unbox_usize(v_i_1769_);
lean_dec(v_i_1769_);
v_stop_boxed_1773_ = lean_unbox_usize(v_stop_1770_);
lean_dec(v_stop_1770_);
v_res_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1767_, v_as_1768_, v_i_boxed_1772_, v_stop_boxed_1773_, v_b_1771_);
lean_dec_ref(v_as_1768_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0(lean_object* v_f_1775_, lean_object* v_s_1776_, lean_object* v_a_1777_, lean_object* v_b_1778_){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_a_1777_);
lean_ctor_set(v___x_1779_, 1, v_b_1778_);
v___x_1780_ = lean_apply_2(v_f_1775_, v___x_1779_, v_s_1776_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
v_a_1789_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1780_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1780_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(lean_object* v_map_1797_, lean_object* v_init_1798_, lean_object* v_f_1799_){
_start:
{
lean_object* v___f_1800_; lean_object* v___x_1801_; lean_object* v_a_1802_; 
v___f_1800_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1800_, 0, v_f_1799_);
lean_inc_ref(v_map_1797_);
v___x_1801_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v___f_1800_, v_map_1797_, v_init_1798_);
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref(v___x_1801_);
return v_a_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___boxed(lean_object* v_map_1803_, lean_object* v_init_1804_, lean_object* v_f_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_1803_, v_init_1804_, v_f_1805_);
lean_dec_ref(v_map_1803_);
return v_res_1806_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0(void){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1807_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1(void){
_start:
{
lean_object* v___x_1808_; lean_object* v_m_x27_1809_; 
v___x_1808_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0);
v_m_x27_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_m_x27_1809_, 0, v___x_1808_);
return v_m_x27_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(lean_object* v_m_1810_, lean_object* v_old2new_1811_){
_start:
{
lean_object* v___f_1812_; lean_object* v_m_x27_1813_; lean_object* v___x_1814_; 
v___f_1812_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1812_, 0, v_old2new_1811_);
v_m_x27_1813_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
v___x_1814_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_m_1810_, v_m_x27_1813_, v___f_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___boxed(lean_object* v_m_1815_, lean_object* v_old2new_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(v_m_1815_, v_old2new_1816_);
lean_dec_ref(v_m_1815_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0(lean_object* v_00_u03b2_1818_, lean_object* v_x_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_x_1819_, v_x_1820_, v_x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(lean_object* v_00_u03c3_1823_, lean_object* v_00_u03b2_1824_, lean_object* v_map_1825_, lean_object* v_init_1826_, lean_object* v_f_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_1825_, v_init_1826_, v_f_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___boxed(lean_object* v_00_u03c3_1829_, lean_object* v_00_u03b2_1830_, lean_object* v_map_1831_, lean_object* v_init_1832_, lean_object* v_f_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(v_00_u03c3_1829_, v_00_u03b2_1830_, v_map_1831_, v_init_1832_, v_f_1833_);
lean_dec_ref(v_map_1831_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(lean_object* v_00_u03b2_1835_, lean_object* v_x_1836_, size_t v_x_1837_, size_t v_x_1838_, lean_object* v_x_1839_, lean_object* v_x_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1836_, v_x_1837_, v_x_1838_, v_x_1839_, v_x_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_, lean_object* v_x_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
size_t v_x_2093__boxed_1848_; size_t v_x_2094__boxed_1849_; lean_object* v_res_1850_; 
v_x_2093__boxed_1848_ = lean_unbox_usize(v_x_1844_);
lean_dec(v_x_1844_);
v_x_2094__boxed_1849_ = lean_unbox_usize(v_x_1845_);
lean_dec(v_x_1845_);
v_res_1850_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(v_00_u03b2_1842_, v_x_1843_, v_x_2093__boxed_1848_, v_x_2094__boxed_1849_, v_x_1846_, v_x_1847_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2___redArg(lean_object* v_map_1851_, lean_object* v_f_1852_, lean_object* v_init_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1852_, v_map_1851_, v_init_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2(lean_object* v_00_u03c3_1855_, lean_object* v_00_u03c3_1856_, lean_object* v_00_u03b2_1857_, lean_object* v_map_1858_, lean_object* v_f_1859_, lean_object* v_init_1860_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1859_, v_map_1858_, v_init_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1862_, lean_object* v_n_1863_, lean_object* v_k_1864_, lean_object* v_v_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v_n_1863_, v_k_1864_, v_v_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1867_, size_t v_depth_1868_, lean_object* v_keys_1869_, lean_object* v_vals_1870_, lean_object* v_heq_1871_, lean_object* v_i_1872_, lean_object* v_entries_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_1868_, v_keys_1869_, v_vals_1870_, v_i_1872_, v_entries_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1875_, lean_object* v_depth_1876_, lean_object* v_keys_1877_, lean_object* v_vals_1878_, lean_object* v_heq_1879_, lean_object* v_i_1880_, lean_object* v_entries_1881_){
_start:
{
size_t v_depth_boxed_1882_; lean_object* v_res_1883_; 
v_depth_boxed_1882_ = lean_unbox_usize(v_depth_1876_);
lean_dec(v_depth_1876_);
v_res_1883_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(v_00_u03b2_1875_, v_depth_boxed_1882_, v_keys_1877_, v_vals_1878_, v_heq_1879_, v_i_1880_, v_entries_1881_);
lean_dec_ref(v_vals_1878_);
lean_dec_ref(v_keys_1877_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5(lean_object* v_00_u03c3_1884_, lean_object* v_00_u03c3_1885_, lean_object* v_00_u03b1_1886_, lean_object* v_00_u03b2_1887_, lean_object* v_f_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1888_, v_x_1889_, v_x_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_, lean_object* v_x_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1893_, v_x_1894_, v_x_1895_, v_x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_1898_, lean_object* v_00_u03b2_1899_, lean_object* v_00_u03c3_1900_, lean_object* v_00_u03c3_1901_, lean_object* v_f_1902_, lean_object* v_as_1903_, size_t v_i_1904_, size_t v_stop_1905_, lean_object* v_b_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1902_, v_as_1903_, v_i_1904_, v_stop_1905_, v_b_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1908_, lean_object* v_00_u03b2_1909_, lean_object* v_00_u03c3_1910_, lean_object* v_00_u03c3_1911_, lean_object* v_f_1912_, lean_object* v_as_1913_, lean_object* v_i_1914_, lean_object* v_stop_1915_, lean_object* v_b_1916_){
_start:
{
size_t v_i_boxed_1917_; size_t v_stop_boxed_1918_; lean_object* v_res_1919_; 
v_i_boxed_1917_ = lean_unbox_usize(v_i_1914_);
lean_dec(v_i_1914_);
v_stop_boxed_1918_ = lean_unbox_usize(v_stop_1915_);
lean_dec(v_stop_1915_);
v_res_1919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_1908_, v_00_u03b2_1909_, v_00_u03c3_1910_, v_00_u03c3_1911_, v_f_1912_, v_as_1913_, v_i_boxed_1917_, v_stop_boxed_1918_, v_b_1916_);
lean_dec_ref(v_as_1913_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03c3_1920_, lean_object* v_00_u03c3_1921_, lean_object* v_00_u03b1_1922_, lean_object* v_00_u03b2_1923_, lean_object* v_f_1924_, lean_object* v_keys_1925_, lean_object* v_vals_1926_, lean_object* v_heq_1927_, lean_object* v_i_1928_, lean_object* v_acc_1929_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1924_, v_keys_1925_, v_vals_1926_, v_i_1928_, v_acc_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03c3_1931_, lean_object* v_00_u03c3_1932_, lean_object* v_00_u03b1_1933_, lean_object* v_00_u03b2_1934_, lean_object* v_f_1935_, lean_object* v_keys_1936_, lean_object* v_vals_1937_, lean_object* v_heq_1938_, lean_object* v_i_1939_, lean_object* v_acc_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(v_00_u03c3_1931_, v_00_u03c3_1932_, v_00_u03b1_1933_, v_00_u03b2_1934_, v_f_1935_, v_keys_1936_, v_vals_1937_, v_heq_1938_, v_i_1939_, v_acc_1940_);
lean_dec_ref(v_vals_1937_);
lean_dec_ref(v_keys_1936_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object* v___x_1942_, lean_object* v___x_1943_, lean_object* v_x_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_array_get_borrowed(v___x_1942_, v___x_1943_, v_x_1944_);
lean_inc(v___x_1945_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object* v___x_1946_, lean_object* v___x_1947_, lean_object* v_x_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(v___x_1946_, v___x_1947_, v_x_1948_);
lean_dec(v_x_1948_);
lean_dec_ref(v___x_1947_);
lean_dec(v___x_1946_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(lean_object* v___x_1950_, size_t v_sz_1951_, size_t v_i_1952_, lean_object* v_bs_1953_){
_start:
{
uint8_t v___x_1954_; 
v___x_1954_ = lean_usize_dec_lt(v_i_1952_, v_sz_1951_);
if (v___x_1954_ == 0)
{
return v_bs_1953_;
}
else
{
lean_object* v_v_1955_; lean_object* v___x_1956_; lean_object* v_bs_x27_1957_; lean_object* v___y_1959_; 
v_v_1955_ = lean_array_uget(v_bs_1953_, v_i_1952_);
v___x_1956_ = lean_unsigned_to_nat(0u);
v_bs_x27_1957_ = lean_array_uset(v_bs_1953_, v_i_1952_, v___x_1956_);
if (lean_obj_tag(v_v_1955_) == 0)
{
v___y_1959_ = v_v_1955_;
goto v___jp_1958_;
}
else
{
lean_object* v_val_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_val_1964_ = lean_ctor_get(v_v_1955_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_v_1955_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1966_ = v_v_1955_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_val_1964_);
lean_dec(v_v_1955_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1968_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_val_1964_, v___x_1950_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1968_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
v___y_1959_ = v___x_1970_;
goto v___jp_1958_;
}
}
}
v___jp_1958_:
{
size_t v___x_1960_; size_t v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = ((size_t)1ULL);
v___x_1961_ = lean_usize_add(v_i_1952_, v___x_1960_);
v___x_1962_ = lean_array_uset(v_bs_x27_1957_, v_i_1952_, v___y_1959_);
v_i_1952_ = v___x_1961_;
v_bs_1953_ = v___x_1962_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13___boxed(lean_object* v___x_1973_, lean_object* v_sz_1974_, lean_object* v_i_1975_, lean_object* v_bs_1976_){
_start:
{
size_t v_sz_boxed_1977_; size_t v_i_boxed_1978_; lean_object* v_res_1979_; 
v_sz_boxed_1977_ = lean_unbox_usize(v_sz_1974_);
lean_dec(v_sz_1974_);
v_i_boxed_1978_ = lean_unbox_usize(v_i_1975_);
lean_dec(v_i_1975_);
v_res_1979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(v___x_1973_, v_sz_boxed_1977_, v_i_boxed_1978_, v_bs_1976_);
lean_dec_ref(v___x_1973_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17(lean_object* v___x_1980_, size_t v_sz_1981_, size_t v_i_1982_, lean_object* v_bs_1983_){
_start:
{
uint8_t v___x_1984_; 
v___x_1984_ = lean_usize_dec_lt(v_i_1982_, v_sz_1981_);
if (v___x_1984_ == 0)
{
return v_bs_1983_;
}
else
{
lean_object* v_v_1985_; lean_object* v___x_1986_; lean_object* v_bs_x27_1987_; lean_object* v___x_1988_; size_t v___x_1989_; size_t v___x_1990_; lean_object* v___x_1991_; 
v_v_1985_ = lean_array_uget(v_bs_1983_, v_i_1982_);
v___x_1986_ = lean_unsigned_to_nat(0u);
v_bs_x27_1987_ = lean_array_uset(v_bs_1983_, v_i_1982_, v___x_1986_);
v___x_1988_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v___x_1980_, v_v_1985_);
v___x_1989_ = ((size_t)1ULL);
v___x_1990_ = lean_usize_add(v_i_1982_, v___x_1989_);
v___x_1991_ = lean_array_uset(v_bs_x27_1987_, v_i_1982_, v___x_1988_);
v_i_1982_ = v___x_1990_;
v_bs_1983_ = v___x_1991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(lean_object* v___x_1993_, lean_object* v_x_1994_){
_start:
{
if (lean_obj_tag(v_x_1994_) == 0)
{
lean_object* v_cs_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2005_; 
v_cs_1995_ = lean_ctor_get(v_x_1994_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_x_1994_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1997_ = v_x_1994_;
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_cs_1995_);
lean_dec(v_x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
size_t v_sz_1999_; size_t v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2003_; 
v_sz_1999_ = lean_array_size(v_cs_1995_);
v___x_2000_ = ((size_t)0ULL);
v___x_2001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17(v___x_1993_, v_sz_1999_, v___x_2000_, v_cs_1995_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2001_);
v___x_2003_ = v___x_1997_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
else
{
lean_object* v_vs_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2016_; 
v_vs_2006_ = lean_ctor_get(v_x_1994_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_x_1994_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2008_ = v_x_1994_;
v_isShared_2009_ = v_isSharedCheck_2016_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_vs_2006_);
lean_dec(v_x_1994_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2016_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
size_t v_sz_2010_; size_t v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
v_sz_2010_ = lean_array_size(v_vs_2006_);
v___x_2011_ = ((size_t)0ULL);
v___x_2012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(v___x_1993_, v_sz_2010_, v___x_2011_, v_vs_2006_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2012_);
v___x_2014_ = v___x_2008_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12___boxed(lean_object* v___x_2017_, lean_object* v_x_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v___x_2017_, v_x_2018_);
lean_dec_ref(v___x_2017_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17___boxed(lean_object* v___x_2020_, lean_object* v_sz_2021_, lean_object* v_i_2022_, lean_object* v_bs_2023_){
_start:
{
size_t v_sz_boxed_2024_; size_t v_i_boxed_2025_; lean_object* v_res_2026_; 
v_sz_boxed_2024_ = lean_unbox_usize(v_sz_2021_);
lean_dec(v_sz_2021_);
v_i_boxed_2025_ = lean_unbox_usize(v_i_2022_);
lean_dec(v_i_2022_);
v_res_2026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17(v___x_2020_, v_sz_boxed_2024_, v_i_boxed_2025_, v_bs_2023_);
lean_dec_ref(v___x_2020_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object* v___x_2027_, lean_object* v_t_2028_){
_start:
{
lean_object* v_root_2029_; lean_object* v_tail_2030_; lean_object* v_size_2031_; size_t v_shift_2032_; lean_object* v_tailOff_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2044_; 
v_root_2029_ = lean_ctor_get(v_t_2028_, 0);
v_tail_2030_ = lean_ctor_get(v_t_2028_, 1);
v_size_2031_ = lean_ctor_get(v_t_2028_, 2);
v_shift_2032_ = lean_ctor_get_usize(v_t_2028_, 4);
v_tailOff_2033_ = lean_ctor_get(v_t_2028_, 3);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_t_2028_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2035_ = v_t_2028_;
v_isShared_2036_ = v_isSharedCheck_2044_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_tailOff_2033_);
lean_inc(v_size_2031_);
lean_inc(v_tail_2030_);
lean_inc(v_root_2029_);
lean_dec(v_t_2028_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2044_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; size_t v_sz_2038_; size_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2037_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v___x_2027_, v_root_2029_);
v_sz_2038_ = lean_array_size(v_tail_2030_);
v___x_2039_ = ((size_t)0ULL);
v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(v___x_2027_, v_sz_2038_, v___x_2039_, v_tail_2030_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v___x_2040_);
lean_ctor_set(v___x_2035_, 0, v___x_2037_);
v___x_2042_ = v___x_2035_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_size_2031_);
lean_ctor_set(v_reuseFailAlloc_2043_, 3, v_tailOff_2033_);
lean_ctor_set_usize(v_reuseFailAlloc_2043_, 4, v_shift_2032_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object* v___x_2045_, lean_object* v_t_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2045_, v_t_2046_);
lean_dec_ref(v___x_2045_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(size_t v_sz_2048_, size_t v_i_2049_, lean_object* v_bs_2050_){
_start:
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_usize_dec_lt(v_i_2049_, v_sz_2048_);
if (v___x_2051_ == 0)
{
return v_bs_2050_;
}
else
{
lean_object* v___x_2052_; lean_object* v_bs_x27_2053_; lean_object* v___x_2054_; size_t v___x_2055_; size_t v___x_2056_; lean_object* v___x_2057_; 
v___x_2052_ = lean_unsigned_to_nat(0u);
v_bs_x27_2053_ = lean_array_uset(v_bs_2050_, v_i_2049_, v___x_2052_);
v___x_2054_ = lean_box(1);
v___x_2055_ = ((size_t)1ULL);
v___x_2056_ = lean_usize_add(v_i_2049_, v___x_2055_);
v___x_2057_ = lean_array_uset(v_bs_x27_2053_, v_i_2049_, v___x_2054_);
v_i_2049_ = v___x_2056_;
v_bs_2050_ = v___x_2057_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17___boxed(lean_object* v_sz_2059_, lean_object* v_i_2060_, lean_object* v_bs_2061_){
_start:
{
size_t v_sz_boxed_2062_; size_t v_i_boxed_2063_; lean_object* v_res_2064_; 
v_sz_boxed_2062_ = lean_unbox_usize(v_sz_2059_);
lean_dec(v_sz_2059_);
v_i_boxed_2063_ = lean_unbox_usize(v_i_2060_);
lean_dec(v_i_2060_);
v_res_2064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(v_sz_boxed_2062_, v_i_boxed_2063_, v_bs_2061_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22(size_t v_sz_2065_, size_t v_i_2066_, lean_object* v_bs_2067_){
_start:
{
uint8_t v___x_2068_; 
v___x_2068_ = lean_usize_dec_lt(v_i_2066_, v_sz_2065_);
if (v___x_2068_ == 0)
{
return v_bs_2067_;
}
else
{
lean_object* v_v_2069_; lean_object* v___x_2070_; lean_object* v_bs_x27_2071_; lean_object* v___x_2072_; size_t v___x_2073_; size_t v___x_2074_; lean_object* v___x_2075_; 
v_v_2069_ = lean_array_uget(v_bs_2067_, v_i_2066_);
v___x_2070_ = lean_unsigned_to_nat(0u);
v_bs_x27_2071_ = lean_array_uset(v_bs_2067_, v_i_2066_, v___x_2070_);
v___x_2072_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16(v_v_2069_);
v___x_2073_ = ((size_t)1ULL);
v___x_2074_ = lean_usize_add(v_i_2066_, v___x_2073_);
v___x_2075_ = lean_array_uset(v_bs_x27_2071_, v_i_2066_, v___x_2072_);
v_i_2066_ = v___x_2074_;
v_bs_2067_ = v___x_2075_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16(lean_object* v_x_2077_){
_start:
{
if (lean_obj_tag(v_x_2077_) == 0)
{
lean_object* v_cs_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2088_; 
v_cs_2078_ = lean_ctor_get(v_x_2077_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_x_2077_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2080_ = v_x_2077_;
v_isShared_2081_ = v_isSharedCheck_2088_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_cs_2078_);
lean_dec(v_x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2088_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
size_t v_sz_2082_; size_t v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2086_; 
v_sz_2082_ = lean_array_size(v_cs_2078_);
v___x_2083_ = ((size_t)0ULL);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22(v_sz_2082_, v___x_2083_, v_cs_2078_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2084_);
v___x_2086_ = v___x_2080_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
else
{
lean_object* v_vs_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2099_; 
v_vs_2089_ = lean_ctor_get(v_x_2077_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_x_2077_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2091_ = v_x_2077_;
v_isShared_2092_ = v_isSharedCheck_2099_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_vs_2089_);
lean_dec(v_x_2077_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2099_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
size_t v_sz_2093_; size_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v_sz_2093_ = lean_array_size(v_vs_2089_);
v___x_2094_ = ((size_t)0ULL);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(v_sz_2093_, v___x_2094_, v_vs_2089_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2095_);
v___x_2097_ = v___x_2091_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22___boxed(lean_object* v_sz_2100_, lean_object* v_i_2101_, lean_object* v_bs_2102_){
_start:
{
size_t v_sz_boxed_2103_; size_t v_i_boxed_2104_; lean_object* v_res_2105_; 
v_sz_boxed_2103_ = lean_unbox_usize(v_sz_2100_);
lean_dec(v_sz_2100_);
v_i_boxed_2104_ = lean_unbox_usize(v_i_2101_);
lean_dec(v_i_2101_);
v_res_2105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22(v_sz_boxed_2103_, v_i_boxed_2104_, v_bs_2102_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object* v_t_2106_){
_start:
{
lean_object* v_root_2107_; lean_object* v_tail_2108_; lean_object* v_size_2109_; size_t v_shift_2110_; lean_object* v_tailOff_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2122_; 
v_root_2107_ = lean_ctor_get(v_t_2106_, 0);
v_tail_2108_ = lean_ctor_get(v_t_2106_, 1);
v_size_2109_ = lean_ctor_get(v_t_2106_, 2);
v_shift_2110_ = lean_ctor_get_usize(v_t_2106_, 4);
v_tailOff_2111_ = lean_ctor_get(v_t_2106_, 3);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_t_2106_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2113_ = v_t_2106_;
v_isShared_2114_ = v_isSharedCheck_2122_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_tailOff_2111_);
lean_inc(v_size_2109_);
lean_inc(v_tail_2108_);
lean_inc(v_root_2107_);
lean_dec(v_t_2106_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2122_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; size_t v_sz_2116_; size_t v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2115_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16(v_root_2107_);
v_sz_2116_ = lean_array_size(v_tail_2108_);
v___x_2117_ = ((size_t)0ULL);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(v_sz_2116_, v___x_2117_, v_tail_2108_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 1, v___x_2118_);
lean_ctor_set(v___x_2113_, 0, v___x_2115_);
v___x_2120_ = v___x_2113_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2121_, 2, v_size_2109_);
lean_ctor_set(v_reuseFailAlloc_2121_, 3, v_tailOff_2111_);
lean_ctor_set_usize(v_reuseFailAlloc_2121_, 4, v_shift_2110_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object* v___x_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
if (lean_obj_tag(v_a_2124_) == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = l_List_reverse___redArg(v_a_2125_);
return v___x_2126_;
}
else
{
lean_object* v_head_2127_; lean_object* v_tail_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2138_; 
v_head_2127_ = lean_ctor_get(v_a_2124_, 0);
v_tail_2128_ = lean_ctor_get(v_a_2124_, 1);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_a_2124_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2130_ = v_a_2124_;
v_isShared_2131_ = v_isSharedCheck_2138_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_tail_2128_);
lean_inc(v_head_2127_);
lean_dec(v_a_2124_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2138_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2132_ = lean_unsigned_to_nat(0u);
v___x_2133_ = lean_array_get_borrowed(v___x_2132_, v___x_2123_, v_head_2127_);
lean_dec(v_head_2127_);
lean_inc(v___x_2133_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 1, v_a_2125_);
lean_ctor_set(v___x_2130_, 0, v___x_2133_);
v___x_2135_ = v___x_2130_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_a_2125_);
v___x_2135_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
v_a_2124_ = v_tail_2128_;
v_a_2125_ = v___x_2135_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6___boxed(lean_object* v___x_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(v___x_2139_, v_a_2140_, v_a_2141_);
lean_dec_ref(v___x_2139_);
return v_res_2142_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2143_ = lean_unsigned_to_nat(32u);
v___x_2144_ = lean_mk_empty_array_with_capacity(v___x_2143_);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
return v___x_2145_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1(void){
_start:
{
size_t v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2146_ = ((size_t)5ULL);
v___x_2147_ = lean_unsigned_to_nat(0u);
v___x_2148_ = lean_unsigned_to_nat(32u);
v___x_2149_ = lean_mk_empty_array_with_capacity(v___x_2148_);
v___x_2150_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0);
v___x_2151_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
lean_ctor_set(v___x_2151_, 1, v___x_2149_);
lean_ctor_set(v___x_2151_, 2, v___x_2147_);
lean_ctor_set(v___x_2151_, 3, v___x_2147_);
lean_ctor_set_usize(v___x_2151_, 4, v___x_2146_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(size_t v_sz_2152_, size_t v_i_2153_, lean_object* v_bs_2154_){
_start:
{
uint8_t v___x_2155_; 
v___x_2155_ = lean_usize_dec_lt(v_i_2153_, v_sz_2152_);
if (v___x_2155_ == 0)
{
return v_bs_2154_;
}
else
{
lean_object* v___x_2156_; lean_object* v_bs_x27_2157_; lean_object* v___x_2158_; size_t v___x_2159_; size_t v___x_2160_; lean_object* v___x_2161_; 
v___x_2156_ = lean_unsigned_to_nat(0u);
v_bs_x27_2157_ = lean_array_uset(v_bs_2154_, v_i_2153_, v___x_2156_);
v___x_2158_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1);
v___x_2159_ = ((size_t)1ULL);
v___x_2160_ = lean_usize_add(v_i_2153_, v___x_2159_);
v___x_2161_ = lean_array_uset(v_bs_x27_2157_, v_i_2153_, v___x_2158_);
v_i_2153_ = v___x_2160_;
v_bs_2154_ = v___x_2161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___boxed(lean_object* v_sz_2163_, lean_object* v_i_2164_, lean_object* v_bs_2165_){
_start:
{
size_t v_sz_boxed_2166_; size_t v_i_boxed_2167_; lean_object* v_res_2168_; 
v_sz_boxed_2166_ = lean_unbox_usize(v_sz_2163_);
lean_dec(v_sz_2163_);
v_i_boxed_2167_ = lean_unbox_usize(v_i_2164_);
lean_dec(v_i_2164_);
v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(v_sz_boxed_2166_, v_i_boxed_2167_, v_bs_2165_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13(size_t v_sz_2169_, size_t v_i_2170_, lean_object* v_bs_2171_){
_start:
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_usize_dec_lt(v_i_2170_, v_sz_2169_);
if (v___x_2172_ == 0)
{
return v_bs_2171_;
}
else
{
lean_object* v_v_2173_; lean_object* v___x_2174_; lean_object* v_bs_x27_2175_; lean_object* v___x_2176_; size_t v___x_2177_; size_t v___x_2178_; lean_object* v___x_2179_; 
v_v_2173_ = lean_array_uget(v_bs_2171_, v_i_2170_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v_bs_x27_2175_ = lean_array_uset(v_bs_2171_, v_i_2170_, v___x_2174_);
v___x_2176_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9(v_v_2173_);
v___x_2177_ = ((size_t)1ULL);
v___x_2178_ = lean_usize_add(v_i_2170_, v___x_2177_);
v___x_2179_ = lean_array_uset(v_bs_x27_2175_, v_i_2170_, v___x_2176_);
v_i_2170_ = v___x_2178_;
v_bs_2171_ = v___x_2179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9(lean_object* v_x_2181_){
_start:
{
if (lean_obj_tag(v_x_2181_) == 0)
{
lean_object* v_cs_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2192_; 
v_cs_2182_ = lean_ctor_get(v_x_2181_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_x_2181_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2184_ = v_x_2181_;
v_isShared_2185_ = v_isSharedCheck_2192_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_cs_2182_);
lean_dec(v_x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2192_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
size_t v_sz_2186_; size_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
v_sz_2186_ = lean_array_size(v_cs_2182_);
v___x_2187_ = ((size_t)0ULL);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13(v_sz_2186_, v___x_2187_, v_cs_2182_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2188_);
v___x_2190_ = v___x_2184_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
else
{
lean_object* v_vs_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2203_; 
v_vs_2193_ = lean_ctor_get(v_x_2181_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_x_2181_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2195_ = v_x_2181_;
v_isShared_2196_ = v_isSharedCheck_2203_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_vs_2193_);
lean_dec(v_x_2181_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2203_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
size_t v_sz_2197_; size_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v_sz_2197_ = lean_array_size(v_vs_2193_);
v___x_2198_ = ((size_t)0ULL);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(v_sz_2197_, v___x_2198_, v_vs_2193_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2199_);
v___x_2201_ = v___x_2195_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13___boxed(lean_object* v_sz_2204_, lean_object* v_i_2205_, lean_object* v_bs_2206_){
_start:
{
size_t v_sz_boxed_2207_; size_t v_i_boxed_2208_; lean_object* v_res_2209_; 
v_sz_boxed_2207_ = lean_unbox_usize(v_sz_2204_);
lean_dec(v_sz_2204_);
v_i_boxed_2208_ = lean_unbox_usize(v_i_2205_);
lean_dec(v_i_2205_);
v_res_2209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13(v_sz_boxed_2207_, v_i_boxed_2208_, v_bs_2206_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object* v_t_2210_){
_start:
{
lean_object* v_root_2211_; lean_object* v_tail_2212_; lean_object* v_size_2213_; size_t v_shift_2214_; lean_object* v_tailOff_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2226_; 
v_root_2211_ = lean_ctor_get(v_t_2210_, 0);
v_tail_2212_ = lean_ctor_get(v_t_2210_, 1);
v_size_2213_ = lean_ctor_get(v_t_2210_, 2);
v_shift_2214_ = lean_ctor_get_usize(v_t_2210_, 4);
v_tailOff_2215_ = lean_ctor_get(v_t_2210_, 3);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_t_2210_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2217_ = v_t_2210_;
v_isShared_2218_ = v_isSharedCheck_2226_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_tailOff_2215_);
lean_inc(v_size_2213_);
lean_inc(v_tail_2212_);
lean_inc(v_root_2211_);
lean_dec(v_t_2210_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2226_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; size_t v_sz_2220_; size_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2219_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9(v_root_2211_);
v_sz_2220_ = lean_array_size(v_tail_2212_);
v___x_2221_ = ((size_t)0ULL);
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(v_sz_2220_, v___x_2221_, v_tail_2212_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v___x_2222_);
lean_ctor_set(v___x_2217_, 0, v___x_2219_);
v___x_2224_ = v___x_2217_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_size_2213_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_tailOff_2215_);
lean_ctor_set_usize(v_reuseFailAlloc_2225_, 4, v_shift_2214_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_unsigned_to_nat(32u);
v___x_2228_ = lean_mk_empty_array_with_capacity(v___x_2227_);
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
return v___x_2229_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1(void){
_start:
{
size_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2230_ = ((size_t)5ULL);
v___x_2231_ = lean_unsigned_to_nat(0u);
v___x_2232_ = lean_unsigned_to_nat(32u);
v___x_2233_ = lean_mk_empty_array_with_capacity(v___x_2232_);
v___x_2234_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0);
v___x_2235_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
lean_ctor_set(v___x_2235_, 1, v___x_2233_);
lean_ctor_set(v___x_2235_, 2, v___x_2231_);
lean_ctor_set(v___x_2235_, 3, v___x_2231_);
lean_ctor_set_usize(v___x_2235_, 4, v___x_2230_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(size_t v_sz_2236_, size_t v_i_2237_, lean_object* v_bs_2238_){
_start:
{
uint8_t v___x_2239_; 
v___x_2239_ = lean_usize_dec_lt(v_i_2237_, v_sz_2236_);
if (v___x_2239_ == 0)
{
return v_bs_2238_;
}
else
{
lean_object* v___x_2240_; lean_object* v_bs_x27_2241_; lean_object* v___x_2242_; size_t v___x_2243_; size_t v___x_2244_; lean_object* v___x_2245_; 
v___x_2240_ = lean_unsigned_to_nat(0u);
v_bs_x27_2241_ = lean_array_uset(v_bs_2238_, v_i_2237_, v___x_2240_);
v___x_2242_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1);
v___x_2243_ = ((size_t)1ULL);
v___x_2244_ = lean_usize_add(v_i_2237_, v___x_2243_);
v___x_2245_ = lean_array_uset(v_bs_x27_2241_, v_i_2237_, v___x_2242_);
v_i_2237_ = v___x_2244_;
v_bs_2238_ = v___x_2245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___boxed(lean_object* v_sz_2247_, lean_object* v_i_2248_, lean_object* v_bs_2249_){
_start:
{
size_t v_sz_boxed_2250_; size_t v_i_boxed_2251_; lean_object* v_res_2252_; 
v_sz_boxed_2250_ = lean_unbox_usize(v_sz_2247_);
lean_dec(v_sz_2247_);
v_i_boxed_2251_ = lean_unbox_usize(v_i_2248_);
lean_dec(v_i_2248_);
v_res_2252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_sz_boxed_2250_, v_i_boxed_2251_, v_bs_2249_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9(size_t v_sz_2253_, size_t v_i_2254_, lean_object* v_bs_2255_){
_start:
{
uint8_t v___x_2256_; 
v___x_2256_ = lean_usize_dec_lt(v_i_2254_, v_sz_2253_);
if (v___x_2256_ == 0)
{
return v_bs_2255_;
}
else
{
lean_object* v_v_2257_; lean_object* v___x_2258_; lean_object* v_bs_x27_2259_; lean_object* v___x_2260_; size_t v___x_2261_; size_t v___x_2262_; lean_object* v___x_2263_; 
v_v_2257_ = lean_array_uget(v_bs_2255_, v_i_2254_);
v___x_2258_ = lean_unsigned_to_nat(0u);
v_bs_x27_2259_ = lean_array_uset(v_bs_2255_, v_i_2254_, v___x_2258_);
v___x_2260_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(v_v_2257_);
v___x_2261_ = ((size_t)1ULL);
v___x_2262_ = lean_usize_add(v_i_2254_, v___x_2261_);
v___x_2263_ = lean_array_uset(v_bs_x27_2259_, v_i_2254_, v___x_2260_);
v_i_2254_ = v___x_2262_;
v_bs_2255_ = v___x_2263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(lean_object* v_x_2265_){
_start:
{
if (lean_obj_tag(v_x_2265_) == 0)
{
lean_object* v_cs_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2276_; 
v_cs_2266_ = lean_ctor_get(v_x_2265_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v_x_2265_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2268_ = v_x_2265_;
v_isShared_2269_ = v_isSharedCheck_2276_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_cs_2266_);
lean_dec(v_x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2276_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
size_t v_sz_2270_; size_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
v_sz_2270_ = lean_array_size(v_cs_2266_);
v___x_2271_ = ((size_t)0ULL);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9(v_sz_2270_, v___x_2271_, v_cs_2266_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2272_);
v___x_2274_ = v___x_2268_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
else
{
lean_object* v_vs_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2287_; 
v_vs_2277_ = lean_ctor_get(v_x_2265_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_x_2265_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2279_ = v_x_2265_;
v_isShared_2280_ = v_isSharedCheck_2287_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_vs_2277_);
lean_dec(v_x_2265_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2287_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
size_t v_sz_2281_; size_t v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
v_sz_2281_ = lean_array_size(v_vs_2277_);
v___x_2282_ = ((size_t)0ULL);
v___x_2283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_sz_2281_, v___x_2282_, v_vs_2277_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2283_);
v___x_2285_ = v___x_2279_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9___boxed(lean_object* v_sz_2288_, lean_object* v_i_2289_, lean_object* v_bs_2290_){
_start:
{
size_t v_sz_boxed_2291_; size_t v_i_boxed_2292_; lean_object* v_res_2293_; 
v_sz_boxed_2291_ = lean_unbox_usize(v_sz_2288_);
lean_dec(v_sz_2288_);
v_i_boxed_2292_ = lean_unbox_usize(v_i_2289_);
lean_dec(v_i_2289_);
v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9(v_sz_boxed_2291_, v_i_boxed_2292_, v_bs_2290_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object* v_t_2294_){
_start:
{
lean_object* v_root_2295_; lean_object* v_tail_2296_; lean_object* v_size_2297_; size_t v_shift_2298_; lean_object* v_tailOff_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2310_; 
v_root_2295_ = lean_ctor_get(v_t_2294_, 0);
v_tail_2296_ = lean_ctor_get(v_t_2294_, 1);
v_size_2297_ = lean_ctor_get(v_t_2294_, 2);
v_shift_2298_ = lean_ctor_get_usize(v_t_2294_, 4);
v_tailOff_2299_ = lean_ctor_get(v_t_2294_, 3);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_t_2294_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2301_ = v_t_2294_;
v_isShared_2302_ = v_isSharedCheck_2310_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_tailOff_2299_);
lean_inc(v_size_2297_);
lean_inc(v_tail_2296_);
lean_inc(v_root_2295_);
lean_dec(v_t_2294_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2310_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; size_t v_sz_2304_; size_t v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2303_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(v_root_2295_);
v_sz_2304_ = lean_array_size(v_tail_2296_);
v___x_2305_ = ((size_t)0ULL);
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_sz_2304_, v___x_2305_, v_tail_2296_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 1, v___x_2306_);
lean_ctor_set(v___x_2301_, 0, v___x_2303_);
v___x_2308_ = v___x_2301_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_size_2297_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_tailOff_2299_);
lean_ctor_set_usize(v_reuseFailAlloc_2309_, 4, v_shift_2298_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(size_t v_sz_2311_, size_t v_i_2312_, lean_object* v_bs_2313_){
_start:
{
uint8_t v___x_2314_; 
v___x_2314_ = lean_usize_dec_lt(v_i_2312_, v_sz_2311_);
if (v___x_2314_ == 0)
{
return v_bs_2313_;
}
else
{
lean_object* v___x_2315_; lean_object* v_bs_x27_2316_; lean_object* v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; lean_object* v___x_2320_; 
v___x_2315_ = lean_unsigned_to_nat(0u);
v_bs_x27_2316_ = lean_array_uset(v_bs_2313_, v_i_2312_, v___x_2315_);
v___x_2317_ = lean_box(0);
v___x_2318_ = ((size_t)1ULL);
v___x_2319_ = lean_usize_add(v_i_2312_, v___x_2318_);
v___x_2320_ = lean_array_uset(v_bs_x27_2316_, v_i_2312_, v___x_2317_);
v_i_2312_ = v___x_2319_;
v_bs_2313_ = v___x_2320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4___boxed(lean_object* v_sz_2322_, lean_object* v_i_2323_, lean_object* v_bs_2324_){
_start:
{
size_t v_sz_boxed_2325_; size_t v_i_boxed_2326_; lean_object* v_res_2327_; 
v_sz_boxed_2325_ = lean_unbox_usize(v_sz_2322_);
lean_dec(v_sz_2322_);
v_i_boxed_2326_ = lean_unbox_usize(v_i_2323_);
lean_dec(v_i_2323_);
v_res_2327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(v_sz_boxed_2325_, v_i_boxed_2326_, v_bs_2324_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5(size_t v_sz_2328_, size_t v_i_2329_, lean_object* v_bs_2330_){
_start:
{
uint8_t v___x_2331_; 
v___x_2331_ = lean_usize_dec_lt(v_i_2329_, v_sz_2328_);
if (v___x_2331_ == 0)
{
return v_bs_2330_;
}
else
{
lean_object* v_v_2332_; lean_object* v___x_2333_; lean_object* v_bs_x27_2334_; lean_object* v___x_2335_; size_t v___x_2336_; size_t v___x_2337_; lean_object* v___x_2338_; 
v_v_2332_ = lean_array_uget(v_bs_2330_, v_i_2329_);
v___x_2333_ = lean_unsigned_to_nat(0u);
v_bs_x27_2334_ = lean_array_uset(v_bs_2330_, v_i_2329_, v___x_2333_);
v___x_2335_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3(v_v_2332_);
v___x_2336_ = ((size_t)1ULL);
v___x_2337_ = lean_usize_add(v_i_2329_, v___x_2336_);
v___x_2338_ = lean_array_uset(v_bs_x27_2334_, v_i_2329_, v___x_2335_);
v_i_2329_ = v___x_2337_;
v_bs_2330_ = v___x_2338_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3(lean_object* v_x_2340_){
_start:
{
if (lean_obj_tag(v_x_2340_) == 0)
{
lean_object* v_cs_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2351_; 
v_cs_2341_ = lean_ctor_get(v_x_2340_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_x_2340_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2343_ = v_x_2340_;
v_isShared_2344_ = v_isSharedCheck_2351_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_cs_2341_);
lean_dec(v_x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2351_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
size_t v_sz_2345_; size_t v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v_sz_2345_ = lean_array_size(v_cs_2341_);
v___x_2346_ = ((size_t)0ULL);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5(v_sz_2345_, v___x_2346_, v_cs_2341_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2347_);
v___x_2349_ = v___x_2343_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
else
{
lean_object* v_vs_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2362_; 
v_vs_2352_ = lean_ctor_get(v_x_2340_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_x_2340_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2354_ = v_x_2340_;
v_isShared_2355_ = v_isSharedCheck_2362_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_vs_2352_);
lean_dec(v_x_2340_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2362_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
size_t v_sz_2356_; size_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2360_; 
v_sz_2356_ = lean_array_size(v_vs_2352_);
v___x_2357_ = ((size_t)0ULL);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(v_sz_2356_, v___x_2357_, v_vs_2352_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2358_);
v___x_2360_ = v___x_2354_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_2363_, lean_object* v_i_2364_, lean_object* v_bs_2365_){
_start:
{
size_t v_sz_boxed_2366_; size_t v_i_boxed_2367_; lean_object* v_res_2368_; 
v_sz_boxed_2366_ = lean_unbox_usize(v_sz_2363_);
lean_dec(v_sz_2363_);
v_i_boxed_2367_ = lean_unbox_usize(v_i_2364_);
lean_dec(v_i_2364_);
v_res_2368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5(v_sz_boxed_2366_, v_i_boxed_2367_, v_bs_2365_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object* v_t_2369_){
_start:
{
lean_object* v_root_2370_; lean_object* v_tail_2371_; lean_object* v_size_2372_; size_t v_shift_2373_; lean_object* v_tailOff_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2385_; 
v_root_2370_ = lean_ctor_get(v_t_2369_, 0);
v_tail_2371_ = lean_ctor_get(v_t_2369_, 1);
v_size_2372_ = lean_ctor_get(v_t_2369_, 2);
v_shift_2373_ = lean_ctor_get_usize(v_t_2369_, 4);
v_tailOff_2374_ = lean_ctor_get(v_t_2369_, 3);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_t_2369_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2376_ = v_t_2369_;
v_isShared_2377_ = v_isSharedCheck_2385_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_tailOff_2374_);
lean_inc(v_size_2372_);
lean_inc(v_tail_2371_);
lean_inc(v_root_2370_);
lean_dec(v_t_2369_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2385_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; size_t v_sz_2379_; size_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2378_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3(v_root_2370_);
v_sz_2379_ = lean_array_size(v_tail_2371_);
v___x_2380_ = ((size_t)0ULL);
v___x_2381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(v_sz_2379_, v___x_2380_, v_tail_2371_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 1, v___x_2381_);
lean_ctor_set(v___x_2376_, 0, v___x_2378_);
v___x_2383_ = v___x_2376_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2378_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2384_, 2, v_size_2372_);
lean_ctor_set(v_reuseFailAlloc_2384_, 3, v_tailOff_2374_);
lean_ctor_set_usize(v_reuseFailAlloc_2384_, 4, v_shift_2373_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(lean_object* v_f_2386_, lean_object* v_as_2387_, lean_object* v_i_2388_, lean_object* v_acc_2389_){
_start:
{
lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2390_ = lean_array_get_size(v_as_2387_);
v___x_2391_ = lean_nat_dec_eq(v_i_2388_, v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2392_ = lean_array_fget_borrowed(v_as_2387_, v_i_2388_);
lean_inc(v_f_2386_);
lean_inc(v___x_2392_);
v___x_2393_ = lean_apply_1(v_f_2386_, v___x_2392_);
v___x_2394_ = lean_unsigned_to_nat(1u);
v___x_2395_ = lean_nat_add(v_i_2388_, v___x_2394_);
lean_dec(v_i_2388_);
v___x_2396_ = lean_array_push(v_acc_2389_, v___x_2393_);
v_i_2388_ = v___x_2395_;
v_acc_2389_ = v___x_2396_;
goto _start;
}
else
{
lean_dec(v_i_2388_);
lean_dec(v_f_2386_);
return v_acc_2389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg___boxed(lean_object* v_f_2398_, lean_object* v_as_2399_, lean_object* v_i_2400_, lean_object* v_acc_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(v_f_2398_, v_as_2399_, v_i_2400_, v_acc_2401_);
lean_dec_ref(v_as_2399_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(lean_object* v_f_2403_, lean_object* v_as_2404_){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2405_ = lean_unsigned_to_nat(0u);
v___x_2406_ = lean_array_get_size(v_as_2404_);
v___x_2407_ = lean_mk_empty_array_with_capacity(v___x_2406_);
v___x_2408_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(v_f_2403_, v_as_2404_, v___x_2405_, v___x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg___boxed(lean_object* v_f_2409_, lean_object* v_as_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(v_f_2409_, v_as_2410_);
lean_dec_ref(v_as_2410_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(lean_object* v_f_2412_, size_t v_sz_2413_, size_t v_i_2414_, lean_object* v_bs_2415_){
_start:
{
uint8_t v___x_2416_; 
v___x_2416_ = lean_usize_dec_lt(v_i_2414_, v_sz_2413_);
if (v___x_2416_ == 0)
{
lean_dec(v_f_2412_);
return v_bs_2415_;
}
else
{
lean_object* v_v_2417_; lean_object* v___x_2418_; lean_object* v_bs_x27_2419_; lean_object* v___y_2421_; 
v_v_2417_ = lean_array_uget(v_bs_2415_, v_i_2414_);
v___x_2418_ = lean_unsigned_to_nat(0u);
v_bs_x27_2419_ = lean_array_uset(v_bs_2415_, v_i_2414_, v___x_2418_);
switch(lean_obj_tag(v_v_2417_))
{
case 0:
{
lean_object* v_key_2426_; lean_object* v_val_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2435_; 
v_key_2426_ = lean_ctor_get(v_v_2417_, 0);
v_val_2427_ = lean_ctor_get(v_v_2417_, 1);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_v_2417_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2429_ = v_v_2417_;
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_val_2427_);
lean_inc(v_key_2426_);
lean_dec(v_v_2417_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2435_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
lean_inc(v_f_2412_);
v___x_2431_ = lean_apply_1(v_f_2412_, v_val_2427_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 1, v___x_2431_);
v___x_2433_ = v___x_2429_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_key_2426_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
v___y_2421_ = v___x_2433_;
goto v___jp_2420_;
}
}
}
case 1:
{
lean_object* v_node_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2444_; 
v_node_2436_ = lean_ctor_get(v_v_2417_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_v_2417_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2438_ = v_v_2417_;
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_node_2436_);
lean_dec(v_v_2417_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
lean_inc(v_f_2412_);
v___x_2440_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v_f_2412_, v_node_2436_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v___x_2440_);
v___x_2442_ = v___x_2438_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
v___y_2421_ = v___x_2442_;
goto v___jp_2420_;
}
}
}
default: 
{
lean_object* v___x_2445_; 
v___x_2445_ = lean_box(2);
v___y_2421_ = v___x_2445_;
goto v___jp_2420_;
}
}
v___jp_2420_:
{
size_t v___x_2422_; size_t v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = ((size_t)1ULL);
v___x_2423_ = lean_usize_add(v_i_2414_, v___x_2422_);
v___x_2424_ = lean_array_uset(v_bs_x27_2419_, v_i_2414_, v___y_2421_);
v_i_2414_ = v___x_2423_;
v_bs_2415_ = v___x_2424_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(lean_object* v_f_2446_, lean_object* v_n_2447_){
_start:
{
if (lean_obj_tag(v_n_2447_) == 0)
{
lean_object* v_es_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2458_; 
v_es_2448_ = lean_ctor_get(v_n_2447_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_n_2447_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2450_ = v_n_2447_;
v_isShared_2451_ = v_isSharedCheck_2458_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_es_2448_);
lean_dec(v_n_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2458_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
size_t v_sz_2452_; size_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v_sz_2452_ = lean_array_size(v_es_2448_);
v___x_2453_ = ((size_t)0ULL);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(v_f_2446_, v_sz_2452_, v___x_2453_, v_es_2448_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v___x_2454_);
v___x_2456_ = v___x_2450_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
else
{
lean_object* v_ks_2459_; lean_object* v_vs_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2468_; 
v_ks_2459_ = lean_ctor_get(v_n_2447_, 0);
v_vs_2460_ = lean_ctor_get(v_n_2447_, 1);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_n_2447_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2462_ = v_n_2447_;
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_vs_2460_);
lean_inc(v_ks_2459_);
lean_dec(v_n_2447_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2468_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v_val_2464_; lean_object* v___x_2466_; 
v_val_2464_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(v_f_2446_, v_vs_2460_);
lean_dec_ref(v_vs_2460_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v_val_2464_);
v___x_2466_ = v___x_2462_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_ks_2459_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_val_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg___boxed(lean_object* v_f_2469_, lean_object* v_sz_2470_, lean_object* v_i_2471_, lean_object* v_bs_2472_){
_start:
{
size_t v_sz_boxed_2473_; size_t v_i_boxed_2474_; lean_object* v_res_2475_; 
v_sz_boxed_2473_ = lean_unbox_usize(v_sz_2470_);
lean_dec(v_sz_2470_);
v_i_boxed_2474_ = lean_unbox_usize(v_i_2471_);
lean_dec(v_i_2471_);
v_res_2475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(v_f_2469_, v_sz_boxed_2473_, v_i_boxed_2474_, v_bs_2472_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg___lam__0(lean_object* v_f_2476_, lean_object* v_x_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_apply_1(v_f_2476_, v_x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(lean_object* v_pm_2479_, lean_object* v_f_2480_){
_start:
{
lean_object* v___f_2481_; lean_object* v___x_2482_; 
v___f_2481_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2481_, 0, v_f_2480_);
v___x_2482_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v___f_2481_, v_pm_2479_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object* v___x_2483_, lean_object* v_a_2484_, lean_object* v___f_2485_, lean_object* v___x_2486_, lean_object* v___x_2487_, lean_object* v_s_2488_){
_start:
{
lean_object* v_vars_2489_; lean_object* v_varMap_2490_; lean_object* v_varsHistory_2491_; lean_object* v_natToIntMap_2492_; lean_object* v_natDef_2493_; lean_object* v_dvds_2494_; lean_object* v_lowers_2495_; lean_object* v_uppers_2496_; lean_object* v_diseqs_2497_; lean_object* v_elimEqs_2498_; lean_object* v_elimStack_2499_; lean_object* v_occurs_2500_; lean_object* v_assignment_2501_; lean_object* v_nextCnstrId_2502_; uint8_t v_caseSplits_2503_; lean_object* v_steps_2504_; lean_object* v_conflict_x3f_2505_; lean_object* v_divMod_2506_; uint8_t v_usedCommRing_2507_; lean_object* v_nonlinearOccs_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2530_; 
v_vars_2489_ = lean_ctor_get(v_s_2488_, 0);
v_varMap_2490_ = lean_ctor_get(v_s_2488_, 1);
v_varsHistory_2491_ = lean_ctor_get(v_s_2488_, 2);
v_natToIntMap_2492_ = lean_ctor_get(v_s_2488_, 3);
v_natDef_2493_ = lean_ctor_get(v_s_2488_, 4);
v_dvds_2494_ = lean_ctor_get(v_s_2488_, 5);
v_lowers_2495_ = lean_ctor_get(v_s_2488_, 6);
v_uppers_2496_ = lean_ctor_get(v_s_2488_, 7);
v_diseqs_2497_ = lean_ctor_get(v_s_2488_, 8);
v_elimEqs_2498_ = lean_ctor_get(v_s_2488_, 9);
v_elimStack_2499_ = lean_ctor_get(v_s_2488_, 10);
v_occurs_2500_ = lean_ctor_get(v_s_2488_, 11);
v_assignment_2501_ = lean_ctor_get(v_s_2488_, 12);
v_nextCnstrId_2502_ = lean_ctor_get(v_s_2488_, 13);
v_caseSplits_2503_ = lean_ctor_get_uint8(v_s_2488_, sizeof(void*)*19);
v_steps_2504_ = lean_ctor_get(v_s_2488_, 14);
v_conflict_x3f_2505_ = lean_ctor_get(v_s_2488_, 15);
v_divMod_2506_ = lean_ctor_get(v_s_2488_, 17);
v_usedCommRing_2507_ = lean_ctor_get_uint8(v_s_2488_, sizeof(void*)*19 + 1);
v_nonlinearOccs_2508_ = lean_ctor_get(v_s_2488_, 18);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_s_2488_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v_s_2488_, 16);
lean_dec(v_unused_2531_);
v___x_2510_ = v_s_2488_;
v_isShared_2511_ = v_isSharedCheck_2530_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_nonlinearOccs_2508_);
lean_inc(v_divMod_2506_);
lean_inc(v_conflict_x3f_2505_);
lean_inc(v_steps_2504_);
lean_inc(v_nextCnstrId_2502_);
lean_inc(v_assignment_2501_);
lean_inc(v_occurs_2500_);
lean_inc(v_elimStack_2499_);
lean_inc(v_elimEqs_2498_);
lean_inc(v_diseqs_2497_);
lean_inc(v_uppers_2496_);
lean_inc(v_lowers_2495_);
lean_inc(v_dvds_2494_);
lean_inc(v_natDef_2493_);
lean_inc(v_natToIntMap_2492_);
lean_inc(v_varsHistory_2491_);
lean_inc(v_varMap_2490_);
lean_inc(v_vars_2489_);
lean_dec(v_s_2488_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2530_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
lean_inc_ref(v_a_2484_);
lean_inc_ref(v_vars_2489_);
v___x_2512_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2483_, v_vars_2489_, v_a_2484_);
lean_inc_ref(v___f_2485_);
lean_inc_ref(v_varMap_2490_);
v___x_2513_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(v_varMap_2490_, v___f_2485_);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v_vars_2489_);
lean_ctor_set(v___x_2514_, 1, v_varMap_2490_);
v___x_2515_ = l_Lean_PersistentArray_push___redArg(v_varsHistory_2491_, v___x_2514_);
v___x_2516_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(v_natDef_2493_, v___f_2485_);
v___x_2517_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v_dvds_2494_);
v___x_2518_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_lowers_2495_);
v___x_2519_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_uppers_2496_);
v___x_2520_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v_diseqs_2497_);
v___x_2521_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2486_, v_elimEqs_2498_, v_a_2484_);
v___x_2522_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2487_, v___x_2521_);
v___x_2523_ = lean_box(0);
v___x_2524_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(v___x_2487_, v_elimStack_2499_, v___x_2523_);
v___x_2525_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(v_occurs_2500_);
v___x_2526_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 16, v___x_2526_);
lean_ctor_set(v___x_2510_, 11, v___x_2525_);
lean_ctor_set(v___x_2510_, 10, v___x_2524_);
lean_ctor_set(v___x_2510_, 9, v___x_2522_);
lean_ctor_set(v___x_2510_, 8, v___x_2520_);
lean_ctor_set(v___x_2510_, 7, v___x_2519_);
lean_ctor_set(v___x_2510_, 6, v___x_2518_);
lean_ctor_set(v___x_2510_, 5, v___x_2517_);
lean_ctor_set(v___x_2510_, 4, v___x_2516_);
lean_ctor_set(v___x_2510_, 2, v___x_2515_);
lean_ctor_set(v___x_2510_, 1, v___x_2513_);
lean_ctor_set(v___x_2510_, 0, v___x_2512_);
v___x_2528_ = v___x_2510_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v_natToIntMap_2492_);
lean_ctor_set(v_reuseFailAlloc_2529_, 4, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2529_, 5, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2529_, 6, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2529_, 7, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2529_, 8, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2529_, 9, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2529_, 10, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2529_, 11, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2529_, 12, v_assignment_2501_);
lean_ctor_set(v_reuseFailAlloc_2529_, 13, v_nextCnstrId_2502_);
lean_ctor_set(v_reuseFailAlloc_2529_, 14, v_steps_2504_);
lean_ctor_set(v_reuseFailAlloc_2529_, 15, v_conflict_x3f_2505_);
lean_ctor_set(v_reuseFailAlloc_2529_, 16, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2529_, 17, v_divMod_2506_);
lean_ctor_set(v_reuseFailAlloc_2529_, 18, v_nonlinearOccs_2508_);
lean_ctor_set_uint8(v_reuseFailAlloc_2529_, sizeof(void*)*19, v_caseSplits_2503_);
lean_ctor_set_uint8(v_reuseFailAlloc_2529_, sizeof(void*)*19 + 1, v_usedCommRing_2507_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object* v___x_2532_, lean_object* v_a_2533_, lean_object* v___f_2534_, lean_object* v___x_2535_, lean_object* v___x_2536_, lean_object* v_s_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(v___x_2532_, v_a_2533_, v___f_2534_, v___x_2535_, v___x_2536_, v_s_2537_);
lean_dec_ref(v___x_2536_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object* v___x_2539_, size_t v_sz_2540_, size_t v_i_2541_, lean_object* v_bs_2542_){
_start:
{
uint8_t v___x_2543_; 
v___x_2543_ = lean_usize_dec_lt(v_i_2541_, v_sz_2540_);
if (v___x_2543_ == 0)
{
return v_bs_2542_;
}
else
{
lean_object* v_v_2544_; lean_object* v___x_2545_; lean_object* v_bs_x27_2546_; lean_object* v___x_2547_; size_t v___x_2548_; size_t v___x_2549_; lean_object* v___x_2550_; 
v_v_2544_ = lean_array_uget(v_bs_2542_, v_i_2541_);
v___x_2545_ = lean_unsigned_to_nat(0u);
v_bs_x27_2546_ = lean_array_uset(v_bs_2542_, v_i_2541_, v___x_2545_);
v___x_2547_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_v_2544_, v___x_2539_);
v___x_2548_ = ((size_t)1ULL);
v___x_2549_ = lean_usize_add(v_i_2541_, v___x_2548_);
v___x_2550_ = lean_array_uset(v_bs_x27_2546_, v_i_2541_, v___x_2547_);
v_i_2541_ = v___x_2549_;
v_bs_2542_ = v___x_2550_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object* v___x_2552_, lean_object* v_sz_2553_, lean_object* v_i_2554_, lean_object* v_bs_2555_){
_start:
{
size_t v_sz_boxed_2556_; size_t v_i_boxed_2557_; lean_object* v_res_2558_; 
v_sz_boxed_2556_ = lean_unbox_usize(v_sz_2553_);
lean_dec(v_sz_2553_);
v_i_boxed_2557_ = lean_unbox_usize(v_i_2554_);
lean_dec(v_i_2554_);
v_res_2558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_2552_, v_sz_boxed_2556_, v_i_boxed_2557_, v_bs_2555_);
lean_dec_ref(v___x_2552_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(lean_object* v_as_2559_, size_t v_i_2560_, size_t v_stop_2561_, lean_object* v_b_2562_){
_start:
{
lean_object* v___y_2564_; uint8_t v___x_2568_; 
v___x_2568_ = lean_usize_dec_eq(v_i_2560_, v_stop_2561_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_array_uget_borrowed(v_as_2559_, v_i_2560_);
if (lean_obj_tag(v___x_2569_) == 0)
{
v___y_2564_ = v_b_2562_;
goto v___jp_2563_;
}
else
{
lean_object* v_val_2570_; lean_object* v___x_2571_; 
v_val_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_val_2570_);
v___x_2571_ = lean_array_push(v_b_2562_, v_val_2570_);
v___y_2564_ = v___x_2571_;
goto v___jp_2563_;
}
}
else
{
return v_b_2562_;
}
v___jp_2563_:
{
size_t v___x_2565_; size_t v___x_2566_; 
v___x_2565_ = ((size_t)1ULL);
v___x_2566_ = lean_usize_add(v_i_2560_, v___x_2565_);
v_i_2560_ = v___x_2566_;
v_b_2562_ = v___y_2564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20___boxed(lean_object* v_as_2572_, lean_object* v_i_2573_, lean_object* v_stop_2574_, lean_object* v_b_2575_){
_start:
{
size_t v_i_boxed_2576_; size_t v_stop_boxed_2577_; lean_object* v_res_2578_; 
v_i_boxed_2576_ = lean_unbox_usize(v_i_2573_);
lean_dec(v_i_2573_);
v_stop_boxed_2577_ = lean_unbox_usize(v_stop_2574_);
lean_dec(v_stop_2574_);
v_res_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_as_2572_, v_i_boxed_2576_, v_stop_boxed_2577_, v_b_2575_);
lean_dec_ref(v_as_2572_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(lean_object* v_x_2579_, lean_object* v_x_2580_){
_start:
{
if (lean_obj_tag(v_x_2579_) == 0)
{
lean_object* v_cs_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v_cs_2581_ = lean_ctor_get(v_x_2579_, 0);
v___x_2582_ = lean_unsigned_to_nat(0u);
v___x_2583_ = lean_array_get_size(v_cs_2581_);
v___x_2584_ = lean_nat_dec_lt(v___x_2582_, v___x_2583_);
if (v___x_2584_ == 0)
{
return v_x_2580_;
}
else
{
size_t v___x_2585_; size_t v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = ((size_t)0ULL);
v___x_2586_ = lean_usize_of_nat(v___x_2583_);
v___x_2587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(v_cs_2581_, v___x_2585_, v___x_2586_, v_x_2580_);
return v___x_2587_;
}
}
else
{
lean_object* v_vs_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
v_vs_2588_ = lean_ctor_get(v_x_2579_, 0);
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = lean_array_get_size(v_vs_2588_);
v___x_2591_ = lean_nat_dec_lt(v___x_2589_, v___x_2590_);
if (v___x_2591_ == 0)
{
return v_x_2580_;
}
else
{
size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = ((size_t)0ULL);
v___x_2593_ = lean_usize_of_nat(v___x_2590_);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_vs_2588_, v___x_2592_, v___x_2593_, v_x_2580_);
return v___x_2594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(lean_object* v_as_2595_, size_t v_i_2596_, size_t v_stop_2597_, lean_object* v_b_2598_){
_start:
{
uint8_t v___x_2599_; 
v___x_2599_ = lean_usize_dec_eq(v_i_2596_, v_stop_2597_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; lean_object* v___x_2601_; size_t v___x_2602_; size_t v___x_2603_; 
v___x_2600_ = lean_array_uget_borrowed(v_as_2595_, v_i_2596_);
v___x_2601_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(v___x_2600_, v_b_2598_);
v___x_2602_ = ((size_t)1ULL);
v___x_2603_ = lean_usize_add(v_i_2596_, v___x_2602_);
v_i_2596_ = v___x_2603_;
v_b_2598_ = v___x_2601_;
goto _start;
}
else
{
return v_b_2598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26___boxed(lean_object* v_as_2605_, lean_object* v_i_2606_, lean_object* v_stop_2607_, lean_object* v_b_2608_){
_start:
{
size_t v_i_boxed_2609_; size_t v_stop_boxed_2610_; lean_object* v_res_2611_; 
v_i_boxed_2609_ = lean_unbox_usize(v_i_2606_);
lean_dec(v_i_2606_);
v_stop_boxed_2610_ = lean_unbox_usize(v_stop_2607_);
lean_dec(v_stop_2607_);
v_res_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(v_as_2605_, v_i_boxed_2609_, v_stop_boxed_2610_, v_b_2608_);
lean_dec_ref(v_as_2605_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21___boxed(lean_object* v_x_2612_, lean_object* v_x_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(v_x_2612_, v_x_2613_);
lean_dec_ref(v_x_2612_);
return v_res_2614_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0(void){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(lean_object* v_x_2616_, size_t v_x_2617_, size_t v_x_2618_, lean_object* v_x_2619_){
_start:
{
if (lean_obj_tag(v_x_2616_) == 0)
{
lean_object* v_cs_2620_; lean_object* v___x_2621_; size_t v___x_2622_; lean_object* v_j_2623_; lean_object* v___x_2624_; size_t v___x_2625_; size_t v___x_2626_; size_t v___x_2627_; size_t v___x_2628_; size_t v___x_2629_; size_t v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; 
v_cs_2620_ = lean_ctor_get(v_x_2616_, 0);
v___x_2621_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0);
v___x_2622_ = lean_usize_shift_right(v_x_2617_, v_x_2618_);
v_j_2623_ = lean_usize_to_nat(v___x_2622_);
v___x_2624_ = lean_array_get_borrowed(v___x_2621_, v_cs_2620_, v_j_2623_);
v___x_2625_ = ((size_t)1ULL);
v___x_2626_ = lean_usize_shift_left(v___x_2625_, v_x_2618_);
v___x_2627_ = lean_usize_sub(v___x_2626_, v___x_2625_);
v___x_2628_ = lean_usize_land(v_x_2617_, v___x_2627_);
v___x_2629_ = ((size_t)5ULL);
v___x_2630_ = lean_usize_sub(v_x_2618_, v___x_2629_);
v___x_2631_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(v___x_2624_, v___x_2628_, v___x_2630_, v_x_2619_);
v___x_2632_ = lean_unsigned_to_nat(1u);
v___x_2633_ = lean_nat_add(v_j_2623_, v___x_2632_);
lean_dec(v_j_2623_);
v___x_2634_ = lean_array_get_size(v_cs_2620_);
v___x_2635_ = lean_nat_dec_lt(v___x_2633_, v___x_2634_);
if (v___x_2635_ == 0)
{
lean_dec(v___x_2633_);
return v___x_2631_;
}
else
{
size_t v___x_2636_; size_t v___x_2637_; lean_object* v___x_2638_; 
v___x_2636_ = lean_usize_of_nat(v___x_2633_);
lean_dec(v___x_2633_);
v___x_2637_ = lean_usize_of_nat(v___x_2634_);
v___x_2638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(v_cs_2620_, v___x_2636_, v___x_2637_, v___x_2631_);
return v___x_2638_;
}
}
else
{
lean_object* v_vs_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v_vs_2639_ = lean_ctor_get(v_x_2616_, 0);
v___x_2640_ = lean_usize_to_nat(v_x_2617_);
v___x_2641_ = lean_array_get_size(v_vs_2639_);
v___x_2642_ = lean_nat_dec_lt(v___x_2640_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_dec(v___x_2640_);
return v_x_2619_;
}
else
{
size_t v___x_2643_; size_t v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = lean_usize_of_nat(v___x_2640_);
lean_dec(v___x_2640_);
v___x_2644_ = lean_usize_of_nat(v___x_2641_);
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_vs_2639_, v___x_2643_, v___x_2644_, v_x_2619_);
return v___x_2645_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___boxed(lean_object* v_x_2646_, lean_object* v_x_2647_, lean_object* v_x_2648_, lean_object* v_x_2649_){
_start:
{
size_t v_x_96785__boxed_2650_; size_t v_x_96786__boxed_2651_; lean_object* v_res_2652_; 
v_x_96785__boxed_2650_ = lean_unbox_usize(v_x_2647_);
lean_dec(v_x_2647_);
v_x_96786__boxed_2651_ = lean_unbox_usize(v_x_2648_);
lean_dec(v_x_2648_);
v_res_2652_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(v_x_2646_, v_x_96785__boxed_2650_, v_x_96786__boxed_2651_, v_x_2649_);
lean_dec_ref(v_x_2646_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object* v_t_2653_, lean_object* v_init_2654_, lean_object* v_start_2655_){
_start:
{
lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2656_ = lean_unsigned_to_nat(0u);
v___x_2657_ = lean_nat_dec_eq(v_start_2655_, v___x_2656_);
if (v___x_2657_ == 0)
{
lean_object* v_root_2658_; lean_object* v_tail_2659_; size_t v_shift_2660_; lean_object* v_tailOff_2661_; uint8_t v___x_2662_; 
v_root_2658_ = lean_ctor_get(v_t_2653_, 0);
v_tail_2659_ = lean_ctor_get(v_t_2653_, 1);
v_shift_2660_ = lean_ctor_get_usize(v_t_2653_, 4);
v_tailOff_2661_ = lean_ctor_get(v_t_2653_, 3);
v___x_2662_ = lean_nat_dec_le(v_tailOff_2661_, v_start_2655_);
if (v___x_2662_ == 0)
{
size_t v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2663_ = lean_usize_of_nat(v_start_2655_);
v___x_2664_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(v_root_2658_, v___x_2663_, v_shift_2660_, v_init_2654_);
v___x_2665_ = lean_array_get_size(v_tail_2659_);
v___x_2666_ = lean_nat_dec_lt(v___x_2656_, v___x_2665_);
if (v___x_2666_ == 0)
{
return v___x_2664_;
}
else
{
size_t v___x_2667_; size_t v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = ((size_t)0ULL);
v___x_2668_ = lean_usize_of_nat(v___x_2665_);
v___x_2669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_tail_2659_, v___x_2667_, v___x_2668_, v___x_2664_);
return v___x_2669_;
}
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; 
v___x_2670_ = lean_nat_sub(v_start_2655_, v_tailOff_2661_);
v___x_2671_ = lean_array_get_size(v_tail_2659_);
v___x_2672_ = lean_nat_dec_lt(v___x_2670_, v___x_2671_);
if (v___x_2672_ == 0)
{
lean_dec(v___x_2670_);
return v_init_2654_;
}
else
{
size_t v___x_2673_; size_t v___x_2674_; lean_object* v___x_2675_; 
v___x_2673_ = lean_usize_of_nat(v___x_2670_);
lean_dec(v___x_2670_);
v___x_2674_ = lean_usize_of_nat(v___x_2671_);
v___x_2675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_tail_2659_, v___x_2673_, v___x_2674_, v_init_2654_);
return v___x_2675_;
}
}
}
else
{
lean_object* v_root_2676_; lean_object* v_tail_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v_root_2676_ = lean_ctor_get(v_t_2653_, 0);
v_tail_2677_ = lean_ctor_get(v_t_2653_, 1);
v___x_2678_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(v_root_2676_, v_init_2654_);
v___x_2679_ = lean_array_get_size(v_tail_2677_);
v___x_2680_ = lean_nat_dec_lt(v___x_2656_, v___x_2679_);
if (v___x_2680_ == 0)
{
return v___x_2678_;
}
else
{
size_t v___x_2681_; size_t v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = ((size_t)0ULL);
v___x_2682_ = lean_usize_of_nat(v___x_2679_);
v___x_2683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_tail_2677_, v___x_2681_, v___x_2682_, v___x_2678_);
return v___x_2683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(lean_object* v_t_2684_, lean_object* v_init_2685_, lean_object* v_start_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_t_2684_, v_init_2685_, v_start_2686_);
lean_dec(v_start_2686_);
lean_dec_ref(v_t_2684_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object* v___x_2688_, size_t v_sz_2689_, size_t v_i_2690_, lean_object* v_bs_2691_){
_start:
{
uint8_t v___x_2692_; 
v___x_2692_ = lean_usize_dec_lt(v_i_2690_, v_sz_2689_);
if (v___x_2692_ == 0)
{
return v_bs_2691_;
}
else
{
lean_object* v_v_2693_; lean_object* v___x_2694_; lean_object* v_bs_x27_2695_; lean_object* v___x_2696_; size_t v___x_2697_; size_t v___x_2698_; lean_object* v___x_2699_; 
v_v_2693_ = lean_array_uget(v_bs_2691_, v_i_2690_);
v___x_2694_ = lean_unsigned_to_nat(0u);
v_bs_x27_2695_ = lean_array_uset(v_bs_2691_, v_i_2690_, v___x_2694_);
v___x_2696_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_v_2693_, v___x_2688_);
v___x_2697_ = ((size_t)1ULL);
v___x_2698_ = lean_usize_add(v_i_2690_, v___x_2697_);
v___x_2699_ = lean_array_uset(v_bs_x27_2695_, v_i_2690_, v___x_2696_);
v_i_2690_ = v___x_2698_;
v_bs_2691_ = v___x_2699_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9___boxed(lean_object* v___x_2701_, lean_object* v_sz_2702_, lean_object* v_i_2703_, lean_object* v_bs_2704_){
_start:
{
size_t v_sz_boxed_2705_; size_t v_i_boxed_2706_; lean_object* v_res_2707_; 
v_sz_boxed_2705_ = lean_unbox_usize(v_sz_2702_);
lean_dec(v_sz_2702_);
v_i_boxed_2706_ = lean_unbox_usize(v_i_2703_);
lean_dec(v_i_2703_);
v_res_2707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v___x_2701_, v_sz_boxed_2705_, v_i_boxed_2706_, v_bs_2704_);
lean_dec_ref(v___x_2701_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object* v_as_2708_, size_t v_sz_2709_, size_t v_i_2710_, lean_object* v_b_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
uint8_t v___x_2723_; 
v___x_2723_ = lean_usize_dec_lt(v_i_2710_, v_sz_2709_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; 
v___x_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2724_, 0, v_b_2711_);
return v___x_2724_;
}
else
{
lean_object* v___x_2725_; lean_object* v_a_2726_; lean_object* v___x_2727_; 
v___x_2725_ = lean_box(0);
v_a_2726_ = lean_array_uget_borrowed(v_as_2708_, v_i_2710_);
lean_inc_ref(v___y_2720_);
lean_inc(v_a_2726_);
v___x_2727_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_a_2726_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
if (lean_obj_tag(v___x_2727_) == 0)
{
size_t v___x_2728_; size_t v___x_2729_; 
lean_dec_ref_known(v___x_2727_, 1);
v___x_2728_ = ((size_t)1ULL);
v___x_2729_ = lean_usize_add(v_i_2710_, v___x_2728_);
v_i_2710_ = v___x_2729_;
v_b_2711_ = v___x_2725_;
goto _start;
}
else
{
return v___x_2727_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object* v_as_2731_, lean_object* v_sz_2732_, lean_object* v_i_2733_, lean_object* v_b_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
size_t v_sz_boxed_2746_; size_t v_i_boxed_2747_; lean_object* v_res_2748_; 
v_sz_boxed_2746_ = lean_unbox_usize(v_sz_2732_);
lean_dec(v_sz_2732_);
v_i_boxed_2747_ = lean_unbox_usize(v_i_2733_);
lean_dec(v_i_2733_);
v_res_2748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v_as_2731_, v_sz_boxed_2746_, v_i_boxed_2747_, v_b_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v_as_2731_);
return v_res_2748_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object* v___x_2749_, uint8_t v___x_2750_, lean_object* v_a_2751_, uint8_t v___x_2752_, lean_object* v_x_2753_){
_start:
{
if (lean_obj_tag(v_x_2753_) == 0)
{
uint8_t v___x_2754_; 
v___x_2754_ = 0;
return v___x_2754_;
}
else
{
lean_object* v_head_2755_; lean_object* v_tail_2756_; uint8_t v___y_2758_; lean_object* v___x_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; 
v_head_2755_ = lean_ctor_get(v_x_2753_, 0);
v_tail_2756_ = lean_ctor_get(v_x_2753_, 1);
v___x_2760_ = lean_unsigned_to_nat(0u);
v___x_2761_ = lean_array_get_borrowed(v___x_2760_, v___x_2749_, v_head_2755_);
v___x_2762_ = lean_nat_dec_eq(v___x_2761_, v_head_2755_);
if (v___x_2762_ == 0)
{
if (v___x_2750_ == 0)
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v___x_2763_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_2764_ = lean_unsigned_to_nat(1u);
v___x_2765_ = lean_array_get_borrowed(v___x_2763_, v_a_2751_, v_head_2755_);
v___x_2766_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_2765_);
v___x_2767_ = lean_nat_dec_lt(v___x_2764_, v___x_2766_);
lean_dec(v___x_2766_);
v___y_2758_ = v___x_2767_;
goto v___jp_2757_;
}
else
{
return v___x_2750_;
}
}
else
{
v___y_2758_ = v___x_2752_;
goto v___jp_2757_;
}
v___jp_2757_:
{
if (v___y_2758_ == 0)
{
v_x_2753_ = v_tail_2756_;
goto _start;
}
else
{
return v___y_2758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___boxed(lean_object* v___x_2768_, lean_object* v___x_2769_, lean_object* v_a_2770_, lean_object* v___x_2771_, lean_object* v_x_2772_){
_start:
{
uint8_t v___x_96958__boxed_2773_; uint8_t v___x_96960__boxed_2774_; uint8_t v_res_2775_; lean_object* v_r_2776_; 
v___x_96958__boxed_2773_ = lean_unbox(v___x_2769_);
v___x_96960__boxed_2774_ = lean_unbox(v___x_2771_);
v_res_2775_ = l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(v___x_2768_, v___x_96958__boxed_2773_, v_a_2770_, v___x_96960__boxed_2774_, v_x_2772_);
lean_dec(v_x_2772_);
lean_dec_ref(v_a_2770_);
lean_dec_ref(v___x_2768_);
v_r_2776_ = lean_box(v_res_2775_);
return v_r_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(lean_object* v_as_2777_, size_t v_i_2778_, size_t v_stop_2779_, lean_object* v_b_2780_){
_start:
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_usize_dec_eq(v_i_2778_, v_stop_2779_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; size_t v___x_2785_; size_t v___x_2786_; 
v___x_2782_ = lean_array_uget_borrowed(v_as_2777_, v_i_2778_);
v___x_2783_ = l_Lean_PersistentArray_toArray___redArg(v___x_2782_);
v___x_2784_ = l_Array_append___redArg(v_b_2780_, v___x_2783_);
lean_dec_ref(v___x_2783_);
v___x_2785_ = ((size_t)1ULL);
v___x_2786_ = lean_usize_add(v_i_2778_, v___x_2785_);
v_i_2778_ = v___x_2786_;
v_b_2780_ = v___x_2784_;
goto _start;
}
else
{
return v_b_2780_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___boxed(lean_object* v_as_2788_, lean_object* v_i_2789_, lean_object* v_stop_2790_, lean_object* v_b_2791_){
_start:
{
size_t v_i_boxed_2792_; size_t v_stop_boxed_2793_; lean_object* v_res_2794_; 
v_i_boxed_2792_ = lean_unbox_usize(v_i_2789_);
lean_dec(v_i_2789_);
v_stop_boxed_2793_ = lean_unbox_usize(v_stop_2790_);
lean_dec(v_stop_2790_);
v_res_2794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_as_2788_, v_i_boxed_2792_, v_stop_boxed_2793_, v_b_2791_);
lean_dec_ref(v_as_2788_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(lean_object* v_x_2795_, lean_object* v_x_2796_){
_start:
{
if (lean_obj_tag(v_x_2795_) == 0)
{
lean_object* v_cs_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v_cs_2797_ = lean_ctor_get(v_x_2795_, 0);
v___x_2798_ = lean_unsigned_to_nat(0u);
v___x_2799_ = lean_array_get_size(v_cs_2797_);
v___x_2800_ = lean_nat_dec_lt(v___x_2798_, v___x_2799_);
if (v___x_2800_ == 0)
{
return v_x_2796_;
}
else
{
size_t v___x_2801_; size_t v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = ((size_t)0ULL);
v___x_2802_ = lean_usize_of_nat(v___x_2799_);
v___x_2803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(v_cs_2797_, v___x_2801_, v___x_2802_, v_x_2796_);
return v___x_2803_;
}
}
else
{
lean_object* v_vs_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; 
v_vs_2804_ = lean_ctor_get(v_x_2795_, 0);
v___x_2805_ = lean_unsigned_to_nat(0u);
v___x_2806_ = lean_array_get_size(v_vs_2804_);
v___x_2807_ = lean_nat_dec_lt(v___x_2805_, v___x_2806_);
if (v___x_2807_ == 0)
{
return v_x_2796_;
}
else
{
size_t v___x_2808_; size_t v___x_2809_; lean_object* v___x_2810_; 
v___x_2808_ = ((size_t)0ULL);
v___x_2809_ = lean_usize_of_nat(v___x_2806_);
v___x_2810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_vs_2804_, v___x_2808_, v___x_2809_, v_x_2796_);
return v___x_2810_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(lean_object* v_as_2811_, size_t v_i_2812_, size_t v_stop_2813_, lean_object* v_b_2814_){
_start:
{
uint8_t v___x_2815_; 
v___x_2815_ = lean_usize_dec_eq(v_i_2812_, v_stop_2813_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; lean_object* v___x_2817_; size_t v___x_2818_; size_t v___x_2819_; 
v___x_2816_ = lean_array_uget_borrowed(v_as_2811_, v_i_2812_);
v___x_2817_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(v___x_2816_, v_b_2814_);
v___x_2818_ = ((size_t)1ULL);
v___x_2819_ = lean_usize_add(v_i_2812_, v___x_2818_);
v_i_2812_ = v___x_2819_;
v_b_2814_ = v___x_2817_;
goto _start;
}
else
{
return v_b_2814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32___boxed(lean_object* v_as_2821_, lean_object* v_i_2822_, lean_object* v_stop_2823_, lean_object* v_b_2824_){
_start:
{
size_t v_i_boxed_2825_; size_t v_stop_boxed_2826_; lean_object* v_res_2827_; 
v_i_boxed_2825_ = lean_unbox_usize(v_i_2822_);
lean_dec(v_i_2822_);
v_stop_boxed_2826_ = lean_unbox_usize(v_stop_2823_);
lean_dec(v_stop_2823_);
v_res_2827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(v_as_2821_, v_i_boxed_2825_, v_stop_boxed_2826_, v_b_2824_);
lean_dec_ref(v_as_2821_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26___boxed(lean_object* v_x_2828_, lean_object* v_x_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(v_x_2828_, v_x_2829_);
lean_dec_ref(v_x_2828_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(lean_object* v_x_2831_, size_t v_x_2832_, size_t v_x_2833_, lean_object* v_x_2834_){
_start:
{
if (lean_obj_tag(v_x_2831_) == 0)
{
lean_object* v_cs_2835_; lean_object* v___x_2836_; size_t v___x_2837_; lean_object* v_j_2838_; lean_object* v___x_2839_; size_t v___x_2840_; size_t v___x_2841_; size_t v___x_2842_; size_t v___x_2843_; size_t v___x_2844_; size_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v_cs_2835_ = lean_ctor_get(v_x_2831_, 0);
v___x_2836_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0);
v___x_2837_ = lean_usize_shift_right(v_x_2832_, v_x_2833_);
v_j_2838_ = lean_usize_to_nat(v___x_2837_);
v___x_2839_ = lean_array_get_borrowed(v___x_2836_, v_cs_2835_, v_j_2838_);
v___x_2840_ = ((size_t)1ULL);
v___x_2841_ = lean_usize_shift_left(v___x_2840_, v_x_2833_);
v___x_2842_ = lean_usize_sub(v___x_2841_, v___x_2840_);
v___x_2843_ = lean_usize_land(v_x_2832_, v___x_2842_);
v___x_2844_ = ((size_t)5ULL);
v___x_2845_ = lean_usize_sub(v_x_2833_, v___x_2844_);
v___x_2846_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(v___x_2839_, v___x_2843_, v___x_2845_, v_x_2834_);
v___x_2847_ = lean_unsigned_to_nat(1u);
v___x_2848_ = lean_nat_add(v_j_2838_, v___x_2847_);
lean_dec(v_j_2838_);
v___x_2849_ = lean_array_get_size(v_cs_2835_);
v___x_2850_ = lean_nat_dec_lt(v___x_2848_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_dec(v___x_2848_);
return v___x_2846_;
}
else
{
size_t v___x_2851_; size_t v___x_2852_; lean_object* v___x_2853_; 
v___x_2851_ = lean_usize_of_nat(v___x_2848_);
lean_dec(v___x_2848_);
v___x_2852_ = lean_usize_of_nat(v___x_2849_);
v___x_2853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(v_cs_2835_, v___x_2851_, v___x_2852_, v___x_2846_);
return v___x_2853_;
}
}
else
{
lean_object* v_vs_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; 
v_vs_2854_ = lean_ctor_get(v_x_2831_, 0);
v___x_2855_ = lean_usize_to_nat(v_x_2832_);
v___x_2856_ = lean_array_get_size(v_vs_2854_);
v___x_2857_ = lean_nat_dec_lt(v___x_2855_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_dec(v___x_2855_);
return v_x_2834_;
}
else
{
size_t v___x_2858_; size_t v___x_2859_; lean_object* v___x_2860_; 
v___x_2858_ = lean_usize_of_nat(v___x_2855_);
lean_dec(v___x_2855_);
v___x_2859_ = lean_usize_of_nat(v___x_2856_);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_vs_2854_, v___x_2858_, v___x_2859_, v_x_2834_);
return v___x_2860_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24___boxed(lean_object* v_x_2861_, lean_object* v_x_2862_, lean_object* v_x_2863_, lean_object* v_x_2864_){
_start:
{
size_t v_x_97062__boxed_2865_; size_t v_x_97063__boxed_2866_; lean_object* v_res_2867_; 
v_x_97062__boxed_2865_ = lean_unbox_usize(v_x_2862_);
lean_dec(v_x_2862_);
v_x_97063__boxed_2866_ = lean_unbox_usize(v_x_2863_);
lean_dec(v_x_2863_);
v_res_2867_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(v_x_2861_, v_x_97062__boxed_2865_, v_x_97063__boxed_2866_, v_x_2864_);
lean_dec_ref(v_x_2861_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object* v_t_2868_, lean_object* v_init_2869_, lean_object* v_start_2870_){
_start:
{
lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2871_ = lean_unsigned_to_nat(0u);
v___x_2872_ = lean_nat_dec_eq(v_start_2870_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_object* v_root_2873_; lean_object* v_tail_2874_; size_t v_shift_2875_; lean_object* v_tailOff_2876_; uint8_t v___x_2877_; 
v_root_2873_ = lean_ctor_get(v_t_2868_, 0);
v_tail_2874_ = lean_ctor_get(v_t_2868_, 1);
v_shift_2875_ = lean_ctor_get_usize(v_t_2868_, 4);
v_tailOff_2876_ = lean_ctor_get(v_t_2868_, 3);
v___x_2877_ = lean_nat_dec_le(v_tailOff_2876_, v_start_2870_);
if (v___x_2877_ == 0)
{
size_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2878_ = lean_usize_of_nat(v_start_2870_);
v___x_2879_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(v_root_2873_, v___x_2878_, v_shift_2875_, v_init_2869_);
v___x_2880_ = lean_array_get_size(v_tail_2874_);
v___x_2881_ = lean_nat_dec_lt(v___x_2871_, v___x_2880_);
if (v___x_2881_ == 0)
{
return v___x_2879_;
}
else
{
size_t v___x_2882_; size_t v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = ((size_t)0ULL);
v___x_2883_ = lean_usize_of_nat(v___x_2880_);
v___x_2884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_tail_2874_, v___x_2882_, v___x_2883_, v___x_2879_);
return v___x_2884_;
}
}
else
{
lean_object* v___x_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2885_ = lean_nat_sub(v_start_2870_, v_tailOff_2876_);
v___x_2886_ = lean_array_get_size(v_tail_2874_);
v___x_2887_ = lean_nat_dec_lt(v___x_2885_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_dec(v___x_2885_);
return v_init_2869_;
}
else
{
size_t v___x_2888_; size_t v___x_2889_; lean_object* v___x_2890_; 
v___x_2888_ = lean_usize_of_nat(v___x_2885_);
lean_dec(v___x_2885_);
v___x_2889_ = lean_usize_of_nat(v___x_2886_);
v___x_2890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_tail_2874_, v___x_2888_, v___x_2889_, v_init_2869_);
return v___x_2890_;
}
}
}
else
{
lean_object* v_root_2891_; lean_object* v_tail_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; 
v_root_2891_ = lean_ctor_get(v_t_2868_, 0);
v_tail_2892_ = lean_ctor_get(v_t_2868_, 1);
v___x_2893_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(v_root_2891_, v_init_2869_);
v___x_2894_ = lean_array_get_size(v_tail_2892_);
v___x_2895_ = lean_nat_dec_lt(v___x_2871_, v___x_2894_);
if (v___x_2895_ == 0)
{
return v___x_2893_;
}
else
{
size_t v___x_2896_; size_t v___x_2897_; lean_object* v___x_2898_; 
v___x_2896_ = ((size_t)0ULL);
v___x_2897_ = lean_usize_of_nat(v___x_2894_);
v___x_2898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_tail_2892_, v___x_2896_, v___x_2897_, v___x_2893_);
return v___x_2898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(lean_object* v_t_2899_, lean_object* v_init_2900_, lean_object* v_start_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v_t_2899_, v_init_2900_, v_start_2901_);
lean_dec(v_start_2901_);
lean_dec_ref(v_t_2899_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
if (lean_obj_tag(v_a_2903_) == 0)
{
lean_object* v___x_2905_; 
v___x_2905_ = l_List_reverse___redArg(v_a_2904_);
return v___x_2905_;
}
else
{
lean_object* v_head_2906_; lean_object* v_tail_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2918_; 
v_head_2906_ = lean_ctor_get(v_a_2903_, 0);
v_tail_2907_ = lean_ctor_get(v_a_2903_, 1);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_a_2903_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2909_ = v_a_2903_;
v_isShared_2910_ = v_isSharedCheck_2918_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_tail_2907_);
lean_inc(v_head_2906_);
lean_dec(v_a_2903_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2918_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2915_; 
v___x_2911_ = l_Nat_reprFast(v_head_2906_);
v___x_2912_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
v___x_2913_ = l_Lean_MessageData_ofFormat(v___x_2912_);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 1, v_a_2904_);
lean_ctor_set(v___x_2909_, 0, v___x_2913_);
v___x_2915_ = v___x_2909_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2913_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_a_2904_);
v___x_2915_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
v_a_2903_ = v_tail_2907_;
v_a_2904_ = v___x_2915_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object* v___x_2919_, size_t v_sz_2920_, size_t v_i_2921_, lean_object* v_bs_2922_){
_start:
{
uint8_t v___x_2923_; 
v___x_2923_ = lean_usize_dec_lt(v_i_2921_, v_sz_2920_);
if (v___x_2923_ == 0)
{
return v_bs_2922_;
}
else
{
lean_object* v_v_2924_; lean_object* v___x_2925_; lean_object* v_bs_x27_2926_; lean_object* v___x_2927_; size_t v___x_2928_; size_t v___x_2929_; lean_object* v___x_2930_; 
v_v_2924_ = lean_array_uget(v_bs_2922_, v_i_2921_);
v___x_2925_ = lean_unsigned_to_nat(0u);
v_bs_x27_2926_ = lean_array_uset(v_bs_2922_, v_i_2921_, v___x_2925_);
v___x_2927_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_v_2924_, v___x_2919_);
v___x_2928_ = ((size_t)1ULL);
v___x_2929_ = lean_usize_add(v_i_2921_, v___x_2928_);
v___x_2930_ = lean_array_uset(v_bs_x27_2926_, v_i_2921_, v___x_2927_);
v_i_2921_ = v___x_2929_;
v_bs_2922_ = v___x_2930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(lean_object* v___x_2932_, lean_object* v_sz_2933_, lean_object* v_i_2934_, lean_object* v_bs_2935_){
_start:
{
size_t v_sz_boxed_2936_; size_t v_i_boxed_2937_; lean_object* v_res_2938_; 
v_sz_boxed_2936_ = lean_unbox_usize(v_sz_2933_);
lean_dec(v_sz_2933_);
v_i_boxed_2937_ = lean_unbox_usize(v_i_2934_);
lean_dec(v_i_2934_);
v_res_2938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v___x_2932_, v_sz_boxed_2936_, v_i_boxed_2937_, v_bs_2935_);
lean_dec_ref(v___x_2932_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object* v_as_2939_, size_t v_sz_2940_, size_t v_i_2941_, lean_object* v_b_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
uint8_t v___x_2954_; 
v___x_2954_ = lean_usize_dec_lt(v_i_2941_, v_sz_2940_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2955_, 0, v_b_2942_);
return v___x_2955_;
}
else
{
lean_object* v___x_2956_; lean_object* v_a_2957_; lean_object* v___x_2958_; 
v___x_2956_ = lean_box(0);
v_a_2957_ = lean_array_uget_borrowed(v_as_2939_, v_i_2941_);
lean_inc(v_a_2957_);
v___x_2958_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(v_a_2957_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
if (lean_obj_tag(v___x_2958_) == 0)
{
size_t v___x_2959_; size_t v___x_2960_; 
lean_dec_ref_known(v___x_2958_, 1);
v___x_2959_ = ((size_t)1ULL);
v___x_2960_ = lean_usize_add(v_i_2941_, v___x_2959_);
v_i_2941_ = v___x_2960_;
v_b_2942_ = v___x_2956_;
goto _start;
}
else
{
return v___x_2958_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___boxed(lean_object* v_as_2962_, lean_object* v_sz_2963_, lean_object* v_i_2964_, lean_object* v_b_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
size_t v_sz_boxed_2977_; size_t v_i_boxed_2978_; lean_object* v_res_2979_; 
v_sz_boxed_2977_ = lean_unbox_usize(v_sz_2963_);
lean_dec(v_sz_2963_);
v_i_boxed_2978_ = lean_unbox_usize(v_i_2964_);
lean_dec(v_i_2964_);
v_res_2979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v_as_2962_, v_sz_boxed_2977_, v_i_boxed_2978_, v_b_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v_as_2962_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object* v_as_2980_, size_t v_sz_2981_, size_t v_i_2982_, lean_object* v_b_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
uint8_t v___x_2995_; 
v___x_2995_ = lean_usize_dec_lt(v_i_2982_, v_sz_2981_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
v___x_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2996_, 0, v_b_2983_);
return v___x_2996_;
}
else
{
lean_object* v___x_2997_; lean_object* v_a_2998_; lean_object* v___x_2999_; 
v___x_2997_ = lean_box(0);
v_a_2998_ = lean_array_uget_borrowed(v_as_2980_, v_i_2982_);
lean_inc(v___y_2993_);
lean_inc_ref(v___y_2992_);
lean_inc(v___y_2991_);
lean_inc_ref(v___y_2990_);
lean_inc(v___y_2989_);
lean_inc_ref(v___y_2988_);
lean_inc(v___y_2987_);
lean_inc_ref(v___y_2986_);
lean_inc(v___y_2985_);
lean_inc(v___y_2984_);
lean_inc(v_a_2998_);
v___x_2999_ = lean_grind_cutsat_assert_le(v_a_2998_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
if (lean_obj_tag(v___x_2999_) == 0)
{
size_t v___x_3000_; size_t v___x_3001_; 
lean_dec_ref_known(v___x_2999_, 1);
v___x_3000_ = ((size_t)1ULL);
v___x_3001_ = lean_usize_add(v_i_2982_, v___x_3000_);
v_i_2982_ = v___x_3001_;
v_b_2983_ = v___x_2997_;
goto _start;
}
else
{
return v___x_2999_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object* v_as_3003_, lean_object* v_sz_3004_, lean_object* v_i_3005_, lean_object* v_b_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
size_t v_sz_boxed_3018_; size_t v_i_boxed_3019_; lean_object* v_res_3020_; 
v_sz_boxed_3018_ = lean_unbox_usize(v_sz_3004_);
lean_dec(v_sz_3004_);
v_i_boxed_3019_ = lean_unbox_usize(v_i_3005_);
lean_dec(v_i_3005_);
v_res_3020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v_as_3003_, v_sz_boxed_3018_, v_i_boxed_3019_, v_b_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v_as_3003_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(lean_object* v_as_3021_, size_t v_i_3022_, size_t v_stop_3023_, lean_object* v_b_3024_){
_start:
{
uint8_t v___x_3025_; 
v___x_3025_ = lean_usize_dec_eq(v_i_3022_, v_stop_3023_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; size_t v___x_3029_; size_t v___x_3030_; 
v___x_3026_ = lean_array_uget_borrowed(v_as_3021_, v_i_3022_);
v___x_3027_ = l_Lean_PersistentArray_toArray___redArg(v___x_3026_);
v___x_3028_ = l_Array_append___redArg(v_b_3024_, v___x_3027_);
lean_dec_ref(v___x_3027_);
v___x_3029_ = ((size_t)1ULL);
v___x_3030_ = lean_usize_add(v_i_3022_, v___x_3029_);
v_i_3022_ = v___x_3030_;
v_b_3024_ = v___x_3028_;
goto _start;
}
else
{
return v_b_3024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30___boxed(lean_object* v_as_3032_, lean_object* v_i_3033_, lean_object* v_stop_3034_, lean_object* v_b_3035_){
_start:
{
size_t v_i_boxed_3036_; size_t v_stop_boxed_3037_; lean_object* v_res_3038_; 
v_i_boxed_3036_ = lean_unbox_usize(v_i_3033_);
lean_dec(v_i_3033_);
v_stop_boxed_3037_ = lean_unbox_usize(v_stop_3034_);
lean_dec(v_stop_3034_);
v_res_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_as_3032_, v_i_boxed_3036_, v_stop_boxed_3037_, v_b_3035_);
lean_dec_ref(v_as_3032_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(lean_object* v_x_3039_, lean_object* v_x_3040_){
_start:
{
if (lean_obj_tag(v_x_3039_) == 0)
{
lean_object* v_cs_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
v_cs_3041_ = lean_ctor_get(v_x_3039_, 0);
v___x_3042_ = lean_unsigned_to_nat(0u);
v___x_3043_ = lean_array_get_size(v_cs_3041_);
v___x_3044_ = lean_nat_dec_lt(v___x_3042_, v___x_3043_);
if (v___x_3044_ == 0)
{
return v_x_3040_;
}
else
{
size_t v___x_3045_; size_t v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = ((size_t)0ULL);
v___x_3046_ = lean_usize_of_nat(v___x_3043_);
v___x_3047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(v_cs_3041_, v___x_3045_, v___x_3046_, v_x_3040_);
return v___x_3047_;
}
}
else
{
lean_object* v_vs_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
v_vs_3048_ = lean_ctor_get(v_x_3039_, 0);
v___x_3049_ = lean_unsigned_to_nat(0u);
v___x_3050_ = lean_array_get_size(v_vs_3048_);
v___x_3051_ = lean_nat_dec_lt(v___x_3049_, v___x_3050_);
if (v___x_3051_ == 0)
{
return v_x_3040_;
}
else
{
size_t v___x_3052_; size_t v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = ((size_t)0ULL);
v___x_3053_ = lean_usize_of_nat(v___x_3050_);
v___x_3054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_vs_3048_, v___x_3052_, v___x_3053_, v_x_3040_);
return v___x_3054_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(lean_object* v_as_3055_, size_t v_i_3056_, size_t v_stop_3057_, lean_object* v_b_3058_){
_start:
{
uint8_t v___x_3059_; 
v___x_3059_ = lean_usize_dec_eq(v_i_3056_, v_stop_3057_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; lean_object* v___x_3061_; size_t v___x_3062_; size_t v___x_3063_; 
v___x_3060_ = lean_array_uget_borrowed(v_as_3055_, v_i_3056_);
v___x_3061_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(v___x_3060_, v_b_3058_);
v___x_3062_ = ((size_t)1ULL);
v___x_3063_ = lean_usize_add(v_i_3056_, v___x_3062_);
v_i_3056_ = v___x_3063_;
v_b_3058_ = v___x_3061_;
goto _start;
}
else
{
return v_b_3058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38___boxed(lean_object* v_as_3065_, lean_object* v_i_3066_, lean_object* v_stop_3067_, lean_object* v_b_3068_){
_start:
{
size_t v_i_boxed_3069_; size_t v_stop_boxed_3070_; lean_object* v_res_3071_; 
v_i_boxed_3069_ = lean_unbox_usize(v_i_3066_);
lean_dec(v_i_3066_);
v_stop_boxed_3070_ = lean_unbox_usize(v_stop_3067_);
lean_dec(v_stop_3067_);
v_res_3071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(v_as_3065_, v_i_boxed_3069_, v_stop_boxed_3070_, v_b_3068_);
lean_dec_ref(v_as_3065_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31___boxed(lean_object* v_x_3072_, lean_object* v_x_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(v_x_3072_, v_x_3073_);
lean_dec_ref(v_x_3072_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(lean_object* v_x_3075_, size_t v_x_3076_, size_t v_x_3077_, lean_object* v_x_3078_){
_start:
{
if (lean_obj_tag(v_x_3075_) == 0)
{
lean_object* v_cs_3079_; lean_object* v___x_3080_; size_t v___x_3081_; lean_object* v_j_3082_; lean_object* v___x_3083_; size_t v___x_3084_; size_t v___x_3085_; size_t v___x_3086_; size_t v___x_3087_; size_t v___x_3088_; size_t v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; 
v_cs_3079_ = lean_ctor_get(v_x_3075_, 0);
v___x_3080_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0);
v___x_3081_ = lean_usize_shift_right(v_x_3076_, v_x_3077_);
v_j_3082_ = lean_usize_to_nat(v___x_3081_);
v___x_3083_ = lean_array_get_borrowed(v___x_3080_, v_cs_3079_, v_j_3082_);
v___x_3084_ = ((size_t)1ULL);
v___x_3085_ = lean_usize_shift_left(v___x_3084_, v_x_3077_);
v___x_3086_ = lean_usize_sub(v___x_3085_, v___x_3084_);
v___x_3087_ = lean_usize_land(v_x_3076_, v___x_3086_);
v___x_3088_ = ((size_t)5ULL);
v___x_3089_ = lean_usize_sub(v_x_3077_, v___x_3088_);
v___x_3090_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(v___x_3083_, v___x_3087_, v___x_3089_, v_x_3078_);
v___x_3091_ = lean_unsigned_to_nat(1u);
v___x_3092_ = lean_nat_add(v_j_3082_, v___x_3091_);
lean_dec(v_j_3082_);
v___x_3093_ = lean_array_get_size(v_cs_3079_);
v___x_3094_ = lean_nat_dec_lt(v___x_3092_, v___x_3093_);
if (v___x_3094_ == 0)
{
lean_dec(v___x_3092_);
return v___x_3090_;
}
else
{
size_t v___x_3095_; size_t v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = lean_usize_of_nat(v___x_3092_);
lean_dec(v___x_3092_);
v___x_3096_ = lean_usize_of_nat(v___x_3093_);
v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(v_cs_3079_, v___x_3095_, v___x_3096_, v___x_3090_);
return v___x_3097_;
}
}
else
{
lean_object* v_vs_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v_vs_3098_ = lean_ctor_get(v_x_3075_, 0);
v___x_3099_ = lean_usize_to_nat(v_x_3076_);
v___x_3100_ = lean_array_get_size(v_vs_3098_);
v___x_3101_ = lean_nat_dec_lt(v___x_3099_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_dec(v___x_3099_);
return v_x_3078_;
}
else
{
size_t v___x_3102_; size_t v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = lean_usize_of_nat(v___x_3099_);
lean_dec(v___x_3099_);
v___x_3103_ = lean_usize_of_nat(v___x_3100_);
v___x_3104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_vs_3098_, v___x_3102_, v___x_3103_, v_x_3078_);
return v___x_3104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29___boxed(lean_object* v_x_3105_, lean_object* v_x_3106_, lean_object* v_x_3107_, lean_object* v_x_3108_){
_start:
{
size_t v_x_97376__boxed_3109_; size_t v_x_97377__boxed_3110_; lean_object* v_res_3111_; 
v_x_97376__boxed_3109_ = lean_unbox_usize(v_x_3106_);
lean_dec(v_x_3106_);
v_x_97377__boxed_3110_ = lean_unbox_usize(v_x_3107_);
lean_dec(v_x_3107_);
v_res_3111_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(v_x_3105_, v_x_97376__boxed_3109_, v_x_97377__boxed_3110_, v_x_3108_);
lean_dec_ref(v_x_3105_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object* v_t_3112_, lean_object* v_init_3113_, lean_object* v_start_3114_){
_start:
{
lean_object* v___x_3115_; uint8_t v___x_3116_; 
v___x_3115_ = lean_unsigned_to_nat(0u);
v___x_3116_ = lean_nat_dec_eq(v_start_3114_, v___x_3115_);
if (v___x_3116_ == 0)
{
lean_object* v_root_3117_; lean_object* v_tail_3118_; size_t v_shift_3119_; lean_object* v_tailOff_3120_; uint8_t v___x_3121_; 
v_root_3117_ = lean_ctor_get(v_t_3112_, 0);
v_tail_3118_ = lean_ctor_get(v_t_3112_, 1);
v_shift_3119_ = lean_ctor_get_usize(v_t_3112_, 4);
v_tailOff_3120_ = lean_ctor_get(v_t_3112_, 3);
v___x_3121_ = lean_nat_dec_le(v_tailOff_3120_, v_start_3114_);
if (v___x_3121_ == 0)
{
size_t v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; uint8_t v___x_3125_; 
v___x_3122_ = lean_usize_of_nat(v_start_3114_);
v___x_3123_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(v_root_3117_, v___x_3122_, v_shift_3119_, v_init_3113_);
v___x_3124_ = lean_array_get_size(v_tail_3118_);
v___x_3125_ = lean_nat_dec_lt(v___x_3115_, v___x_3124_);
if (v___x_3125_ == 0)
{
return v___x_3123_;
}
else
{
size_t v___x_3126_; size_t v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = ((size_t)0ULL);
v___x_3127_ = lean_usize_of_nat(v___x_3124_);
v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_tail_3118_, v___x_3126_, v___x_3127_, v___x_3123_);
return v___x_3128_;
}
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
v___x_3129_ = lean_nat_sub(v_start_3114_, v_tailOff_3120_);
v___x_3130_ = lean_array_get_size(v_tail_3118_);
v___x_3131_ = lean_nat_dec_lt(v___x_3129_, v___x_3130_);
if (v___x_3131_ == 0)
{
lean_dec(v___x_3129_);
return v_init_3113_;
}
else
{
size_t v___x_3132_; size_t v___x_3133_; lean_object* v___x_3134_; 
v___x_3132_ = lean_usize_of_nat(v___x_3129_);
lean_dec(v___x_3129_);
v___x_3133_ = lean_usize_of_nat(v___x_3130_);
v___x_3134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_tail_3118_, v___x_3132_, v___x_3133_, v_init_3113_);
return v___x_3134_;
}
}
}
else
{
lean_object* v_root_3135_; lean_object* v_tail_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v_root_3135_ = lean_ctor_get(v_t_3112_, 0);
v_tail_3136_ = lean_ctor_get(v_t_3112_, 1);
v___x_3137_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(v_root_3135_, v_init_3113_);
v___x_3138_ = lean_array_get_size(v_tail_3136_);
v___x_3139_ = lean_nat_dec_lt(v___x_3115_, v___x_3138_);
if (v___x_3139_ == 0)
{
return v___x_3137_;
}
else
{
size_t v___x_3140_; size_t v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = ((size_t)0ULL);
v___x_3141_ = lean_usize_of_nat(v___x_3138_);
v___x_3142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_tail_3136_, v___x_3140_, v___x_3141_, v___x_3137_);
return v___x_3142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object* v_t_3143_, lean_object* v_init_3144_, lean_object* v_start_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v_t_3143_, v_init_3144_, v_start_3145_);
lean_dec(v_start_3145_);
lean_dec_ref(v_t_3143_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(lean_object* v_msgData_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v___x_3153_; lean_object* v_env_3154_; uint8_t v___x_3155_; lean_object* v_env_3156_; lean_object* v___x_3157_; lean_object* v_toCold_3158_; lean_object* v_mctx_3159_; lean_object* v_lctx_3160_; lean_object* v_options_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3153_ = lean_st_ref_get(v___y_3151_);
v_env_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc_ref(v_env_3154_);
lean_dec(v___x_3153_);
v___x_3155_ = 0;
v_env_3156_ = l_Lean_Environment_setRecordingDeps(v_env_3154_, v___x_3155_);
v___x_3157_ = lean_st_ref_get(v___y_3149_);
v_toCold_3158_ = lean_ctor_get(v___y_3150_, 0);
v_mctx_3159_ = lean_ctor_get(v___x_3157_, 0);
lean_inc_ref(v_mctx_3159_);
lean_dec(v___x_3157_);
v_lctx_3160_ = lean_ctor_get(v___y_3148_, 2);
v_options_3161_ = lean_ctor_get(v_toCold_3158_, 2);
lean_inc_ref(v_options_3161_);
lean_inc_ref(v_lctx_3160_);
v___x_3162_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3162_, 0, v_env_3156_);
lean_ctor_set(v___x_3162_, 1, v_mctx_3159_);
lean_ctor_set(v___x_3162_, 2, v_lctx_3160_);
lean_ctor_set(v___x_3162_, 3, v_options_3161_);
v___x_3163_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
lean_ctor_set(v___x_3163_, 1, v_msgData_3147_);
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38___boxed(lean_object* v_msgData_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(v_msgData_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
return v_res_3171_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0(void){
_start:
{
lean_object* v___x_3172_; double v___x_3173_; 
v___x_3172_ = lean_unsigned_to_nat(0u);
v___x_3173_ = lean_float_of_nat(v___x_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(lean_object* v_cls_3177_, lean_object* v_msg_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_ref_3184_; lean_object* v___x_3185_; lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3231_; 
v_ref_3184_ = lean_ctor_get(v___y_3181_, 2);
v___x_3185_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(v_msg_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3188_ = v___x_3185_;
v_isShared_3189_ = v_isSharedCheck_3231_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3185_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3231_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v_traceState_3191_; lean_object* v_env_3192_; lean_object* v_nextMacroScope_3193_; lean_object* v_ngen_3194_; lean_object* v_auxDeclNGen_3195_; lean_object* v_cache_3196_; lean_object* v_recordedDeps_3197_; lean_object* v_messages_3198_; lean_object* v_infoState_3199_; lean_object* v_snapshotTasks_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3230_; 
v___x_3190_ = lean_st_ref_take(v___y_3182_);
v_traceState_3191_ = lean_ctor_get(v___x_3190_, 4);
v_env_3192_ = lean_ctor_get(v___x_3190_, 0);
v_nextMacroScope_3193_ = lean_ctor_get(v___x_3190_, 1);
v_ngen_3194_ = lean_ctor_get(v___x_3190_, 2);
v_auxDeclNGen_3195_ = lean_ctor_get(v___x_3190_, 3);
v_cache_3196_ = lean_ctor_get(v___x_3190_, 5);
v_recordedDeps_3197_ = lean_ctor_get(v___x_3190_, 6);
v_messages_3198_ = lean_ctor_get(v___x_3190_, 7);
v_infoState_3199_ = lean_ctor_get(v___x_3190_, 8);
v_snapshotTasks_3200_ = lean_ctor_get(v___x_3190_, 9);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3202_ = v___x_3190_;
v_isShared_3203_ = v_isSharedCheck_3230_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_snapshotTasks_3200_);
lean_inc(v_infoState_3199_);
lean_inc(v_messages_3198_);
lean_inc(v_recordedDeps_3197_);
lean_inc(v_cache_3196_);
lean_inc(v_traceState_3191_);
lean_inc(v_auxDeclNGen_3195_);
lean_inc(v_ngen_3194_);
lean_inc(v_nextMacroScope_3193_);
lean_inc(v_env_3192_);
lean_dec(v___x_3190_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3230_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
uint64_t v_tid_3204_; lean_object* v_traces_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3229_; 
v_tid_3204_ = lean_ctor_get_uint64(v_traceState_3191_, sizeof(void*)*1);
v_traces_3205_ = lean_ctor_get(v_traceState_3191_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_traceState_3191_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3207_ = v_traceState_3191_;
v_isShared_3208_ = v_isSharedCheck_3229_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_traces_3205_);
lean_dec(v_traceState_3191_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3229_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; double v___x_3211_; uint8_t v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3220_; 
v___x_3209_ = lean_box(0);
v___x_3210_ = lean_box(0);
v___x_3211_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0);
v___x_3212_ = 0;
v___x_3213_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1));
v___x_3214_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3214_, 0, v_cls_3177_);
lean_ctor_set(v___x_3214_, 1, v___x_3210_);
lean_ctor_set(v___x_3214_, 2, v___x_3213_);
lean_ctor_set_float(v___x_3214_, sizeof(void*)*3, v___x_3211_);
lean_ctor_set_float(v___x_3214_, sizeof(void*)*3 + 8, v___x_3211_);
lean_ctor_set_uint8(v___x_3214_, sizeof(void*)*3 + 16, v___x_3212_);
v___x_3215_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2));
v___x_3216_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3214_);
lean_ctor_set(v___x_3216_, 1, v_a_3186_);
lean_ctor_set(v___x_3216_, 2, v___x_3215_);
lean_inc(v_ref_3184_);
v___x_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3217_, 0, v_ref_3184_);
lean_ctor_set(v___x_3217_, 1, v___x_3216_);
v___x_3218_ = l_Lean_PersistentArray_push___redArg(v_traces_3205_, v___x_3217_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v___x_3218_);
v___x_3220_ = v___x_3207_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3218_);
lean_ctor_set_uint64(v_reuseFailAlloc_3228_, sizeof(void*)*1, v_tid_3204_);
v___x_3220_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___x_3222_; 
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 4, v___x_3220_);
v___x_3222_ = v___x_3202_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_env_3192_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_nextMacroScope_3193_);
lean_ctor_set(v_reuseFailAlloc_3227_, 2, v_ngen_3194_);
lean_ctor_set(v_reuseFailAlloc_3227_, 3, v_auxDeclNGen_3195_);
lean_ctor_set(v_reuseFailAlloc_3227_, 4, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3227_, 5, v_cache_3196_);
lean_ctor_set(v_reuseFailAlloc_3227_, 6, v_recordedDeps_3197_);
lean_ctor_set(v_reuseFailAlloc_3227_, 7, v_messages_3198_);
lean_ctor_set(v_reuseFailAlloc_3227_, 8, v_infoState_3199_);
lean_ctor_set(v_reuseFailAlloc_3227_, 9, v_snapshotTasks_3200_);
v___x_3222_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3223_ = lean_st_ref_put(v___y_3182_, v___x_3222_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v___x_3209_);
v___x_3225_ = v___x_3188_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3209_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___boxed(lean_object* v_cls_3232_, lean_object* v_msg_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v_cls_3232_, v_msg_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
return v_res_3239_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3(void){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2));
v___x_3245_ = l_Lean_stringToMessageData(v___x_3244_);
return v___x_3245_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11(void){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3259_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10));
v___x_3260_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1));
v___x_3261_ = l_Lean_Name_append(v___x_3260_, v___x_3259_);
return v___x_3261_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12));
v___x_3264_ = l_Lean_stringToMessageData(v___x_3263_);
return v___x_3264_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15(void){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3269_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14));
v___x_3270_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1));
v___x_3271_ = l_Lean_Name_append(v___x_3270_, v___x_3269_);
return v___x_3271_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__16));
v___x_3274_ = l_Lean_stringToMessageData(v___x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_){
_start:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3286_ = lean_unsigned_to_nat(0u);
v___x_3287_ = l_Lean_instInhabitedExpr;
v___x_3288_ = lean_box(0);
v___x_3289_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3275_, v_a_3283_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3430_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3430_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3430_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v_vars_3294_; lean_object* v_varsHistory_3295_; lean_object* v_dvds_3296_; lean_object* v_lowers_3297_; lean_object* v_uppers_3298_; lean_object* v_diseqs_3299_; uint8_t v___x_3300_; 
v_vars_3294_ = lean_ctor_get(v_a_3290_, 0);
lean_inc_ref(v_vars_3294_);
v_varsHistory_3295_ = lean_ctor_get(v_a_3290_, 2);
lean_inc_ref(v_varsHistory_3295_);
v_dvds_3296_ = lean_ctor_get(v_a_3290_, 5);
lean_inc_ref(v_dvds_3296_);
v_lowers_3297_ = lean_ctor_get(v_a_3290_, 6);
lean_inc_ref(v_lowers_3297_);
v_uppers_3298_ = lean_ctor_get(v_a_3290_, 7);
lean_inc_ref(v_uppers_3298_);
v_diseqs_3299_ = lean_ctor_get(v_a_3290_, 8);
lean_inc_ref(v_diseqs_3299_);
lean_dec(v_a_3290_);
v___x_3300_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_3294_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; 
lean_del_object(v___x_3292_);
v___x_3301_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3303_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3301_, 1);
v___x_3303_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(v_a_3302_, v_a_3275_, v_a_3283_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3409_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3306_ = v___x_3303_;
v_isShared_3307_ = v_isSharedCheck_3409_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3303_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3409_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v_size_3308_; lean_object* v___x_3309_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v_options_3321_; lean_object* v_inheritedTraceOptions_3322_; lean_object* v___y_3323_; uint8_t v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v_size_3308_ = lean_ctor_get(v_vars_3294_, 2);
lean_inc(v_size_3308_);
lean_dec_ref(v_vars_3294_);
v___x_3309_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_a_3304_);
v___x_3336_ = l_Lean_PersistentArray_isEmpty___redArg(v_varsHistory_3295_);
v___x_3337_ = l_List_range(v_size_3308_);
v___x_3338_ = l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(v___x_3309_, v___x_3336_, v_a_3302_, v___x_3300_, v___x_3337_);
lean_dec(v___x_3337_);
lean_dec(v_a_3302_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3341_; 
lean_dec_ref(v___x_3309_);
lean_dec(v_a_3304_);
lean_dec_ref(v_diseqs_3299_);
lean_dec_ref(v_uppers_3298_);
lean_dec_ref(v_lowers_3297_);
lean_dec_ref(v_dvds_3296_);
lean_dec_ref(v_varsHistory_3295_);
v___x_3339_ = lean_box(0);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 0, v___x_3339_);
v___x_3341_ = v___x_3306_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3339_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
else
{
lean_object* v_toCold_3343_; lean_object* v_options_3344_; lean_object* v_inheritedTraceOptions_3345_; uint8_t v_hasTrace_3346_; lean_object* v___f_3347_; lean_object* v___f_3348_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; 
lean_del_object(v___x_3306_);
v_toCold_3343_ = lean_ctor_get(v_a_3283_, 0);
v_options_3344_ = lean_ctor_get(v_toCold_3343_, 2);
v_inheritedTraceOptions_3345_ = lean_ctor_get(v_toCold_3343_, 11);
v_hasTrace_3346_ = lean_ctor_get_uint8(v_options_3344_, sizeof(void*)*1);
lean_inc_ref_n(v___x_3309_, 2);
v___f_3347_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3347_, 0, v___x_3286_);
lean_closure_set(v___f_3347_, 1, v___x_3309_);
lean_inc(v_a_3304_);
v___f_3348_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed), 6, 5);
lean_closure_set(v___f_3348_, 0, v___x_3287_);
lean_closure_set(v___f_3348_, 1, v_a_3304_);
lean_closure_set(v___f_3348_, 2, v___f_3347_);
lean_closure_set(v___f_3348_, 3, v___x_3288_);
lean_closure_set(v___f_3348_, 4, v___x_3309_);
if (v_hasTrace_3346_ == 0)
{
lean_dec_ref(v_varsHistory_3295_);
v___y_3350_ = v_a_3275_;
v___y_3351_ = v_a_3276_;
v___y_3352_ = v_a_3277_;
v___y_3353_ = v_a_3278_;
v___y_3354_ = v_a_3279_;
v___y_3355_ = v_a_3280_;
v___y_3356_ = v_a_3281_;
v___y_3357_ = v_a_3282_;
v___y_3358_ = v_a_3283_;
v___y_3359_ = v_a_3284_;
goto v___jp_3349_;
}
else
{
lean_object* v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
v___x_3397_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14));
v___x_3398_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15);
v___x_3399_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3345_, v_options_3344_, v___x_3398_);
if (v___x_3399_ == 0)
{
lean_dec_ref(v_varsHistory_3295_);
v___y_3350_ = v_a_3275_;
v___y_3351_ = v_a_3276_;
v___y_3352_ = v_a_3277_;
v___y_3353_ = v_a_3278_;
v___y_3354_ = v_a_3279_;
v___y_3355_ = v_a_3280_;
v___y_3356_ = v_a_3281_;
v___y_3357_ = v_a_3282_;
v___y_3358_ = v_a_3283_;
v___y_3359_ = v_a_3284_;
goto v___jp_3349_;
}
else
{
lean_object* v_size_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v_size_3400_ = lean_ctor_get(v_varsHistory_3295_, 2);
lean_inc(v_size_3400_);
lean_dec_ref(v_varsHistory_3295_);
v___x_3401_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17);
v___x_3402_ = lean_unsigned_to_nat(1u);
v___x_3403_ = lean_nat_add(v_size_3400_, v___x_3402_);
lean_dec(v_size_3400_);
v___x_3404_ = l_Nat_reprFast(v___x_3403_);
v___x_3405_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
v___x_3406_ = l_Lean_MessageData_ofFormat(v___x_3405_);
v___x_3407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3401_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___x_3408_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___x_3397_, v___x_3407_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_dec_ref_known(v___x_3408_, 1);
v___y_3350_ = v_a_3275_;
v___y_3351_ = v_a_3276_;
v___y_3352_ = v_a_3277_;
v___y_3353_ = v_a_3278_;
v___y_3354_ = v_a_3279_;
v___y_3355_ = v_a_3280_;
v___y_3356_ = v_a_3281_;
v___y_3357_ = v_a_3282_;
v___y_3358_ = v_a_3283_;
v___y_3359_ = v_a_3284_;
goto v___jp_3349_;
}
else
{
lean_dec_ref(v___f_3348_);
lean_dec_ref(v___x_3309_);
lean_dec(v_a_3304_);
lean_dec_ref(v_diseqs_3299_);
lean_dec_ref(v_uppers_3298_);
lean_dec_ref(v_lowers_3297_);
lean_dec_ref(v_dvds_3296_);
return v___x_3408_;
}
}
}
v___jp_3349_:
{
lean_object* v___x_3360_; 
v___x_3360_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v___x_3361_; lean_object* v___x_3362_; size_t v_sz_3363_; size_t v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; size_t v_sz_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; size_t v_sz_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
lean_dec_ref_known(v___x_3360_, 1);
v___x_3361_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7));
v___x_3362_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_dvds_3296_, v___x_3361_, v___x_3286_);
lean_dec_ref(v_dvds_3296_);
v_sz_3363_ = lean_array_size(v___x_3362_);
v___x_3364_ = ((size_t)0ULL);
v___x_3365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v___x_3309_, v_sz_3363_, v___x_3364_, v___x_3362_);
v___x_3366_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v_lowers_3297_, v___x_3361_, v___x_3286_);
lean_dec_ref(v_lowers_3297_);
v___x_3367_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v_uppers_3298_, v___x_3366_, v___x_3286_);
lean_dec_ref(v_uppers_3298_);
v_sz_3368_ = lean_array_size(v___x_3367_);
v___x_3369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_3309_, v_sz_3368_, v___x_3364_, v___x_3367_);
v___x_3370_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v_diseqs_3299_, v___x_3361_, v___x_3286_);
lean_dec_ref(v_diseqs_3299_);
v_sz_3371_ = lean_array_size(v___x_3370_);
v___x_3372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v___x_3309_, v_sz_3371_, v___x_3364_, v___x_3370_);
v___x_3373_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3374_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3373_, v___f_3348_, v___y_3350_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v___x_3375_; size_t v_sz_3376_; lean_object* v___x_3377_; 
lean_dec_ref_known(v___x_3374_, 1);
v___x_3375_ = lean_box(0);
v_sz_3376_ = lean_array_size(v___x_3365_);
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_3365_, v_sz_3376_, v___x_3364_, v___x_3375_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
lean_dec_ref(v___x_3365_);
if (lean_obj_tag(v___x_3377_) == 0)
{
size_t v_sz_3378_; lean_object* v___x_3379_; 
lean_dec_ref_known(v___x_3377_, 1);
v_sz_3378_ = lean_array_size(v___x_3369_);
v___x_3379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v___x_3369_, v_sz_3378_, v___x_3364_, v___x_3375_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
lean_dec_ref(v___x_3369_);
if (lean_obj_tag(v___x_3379_) == 0)
{
size_t v_sz_3380_; lean_object* v___x_3381_; 
lean_dec_ref_known(v___x_3379_, 1);
v_sz_3380_ = lean_array_size(v___x_3372_);
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v___x_3372_, v_sz_3380_, v___x_3364_, v___x_3375_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
lean_dec_ref(v___x_3372_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_toCold_3382_; lean_object* v_options_3383_; uint8_t v_hasTrace_3384_; 
lean_dec_ref_known(v___x_3381_, 1);
v_toCold_3382_ = lean_ctor_get(v___y_3358_, 0);
v_options_3383_ = lean_ctor_get(v_toCold_3382_, 2);
v_hasTrace_3384_ = lean_ctor_get_uint8(v_options_3383_, sizeof(void*)*1);
if (v_hasTrace_3384_ == 0)
{
lean_object* v___x_3385_; 
lean_dec_ref(v___x_3309_);
lean_dec(v_a_3304_);
v___x_3385_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
return v___x_3385_;
}
else
{
lean_object* v_inheritedTraceOptions_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v_inheritedTraceOptions_3386_ = lean_ctor_get(v_toCold_3382_, 11);
v___x_3387_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10));
v___x_3388_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11);
v___x_3389_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3386_, v_options_3383_, v___x_3388_);
if (v___x_3389_ == 0)
{
lean_dec(v_a_3304_);
v___y_3311_ = v___x_3387_;
v___y_3312_ = v___y_3350_;
v___y_3313_ = v___y_3351_;
v___y_3314_ = v___y_3352_;
v___y_3315_ = v___y_3353_;
v___y_3316_ = v___y_3354_;
v___y_3317_ = v___y_3355_;
v___y_3318_ = v___y_3356_;
v___y_3319_ = v___y_3357_;
v___y_3320_ = v___y_3358_;
v_options_3321_ = v_options_3383_;
v_inheritedTraceOptions_3322_ = v_inheritedTraceOptions_3386_;
v___y_3323_ = v___y_3359_;
goto v___jp_3310_;
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3390_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13);
v___x_3391_ = lean_array_to_list(v_a_3304_);
v___x_3392_ = lean_box(0);
v___x_3393_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(v___x_3391_, v___x_3392_);
v___x_3394_ = l_Lean_MessageData_ofList(v___x_3393_);
v___x_3395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3390_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
v___x_3396_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___x_3387_, v___x_3395_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_dec_ref_known(v___x_3396_, 1);
v___y_3311_ = v___x_3387_;
v___y_3312_ = v___y_3350_;
v___y_3313_ = v___y_3351_;
v___y_3314_ = v___y_3352_;
v___y_3315_ = v___y_3353_;
v___y_3316_ = v___y_3354_;
v___y_3317_ = v___y_3355_;
v___y_3318_ = v___y_3356_;
v___y_3319_ = v___y_3357_;
v___y_3320_ = v___y_3358_;
v_options_3321_ = v_options_3383_;
v_inheritedTraceOptions_3322_ = v_inheritedTraceOptions_3386_;
v___y_3323_ = v___y_3359_;
goto v___jp_3310_;
}
else
{
lean_dec_ref(v___x_3309_);
return v___x_3396_;
}
}
}
}
else
{
lean_dec_ref(v___x_3309_);
lean_dec(v_a_3304_);
return v___x_3381_;
}
}
else
{
lean_dec_ref(v___x_3372_);
lean_dec_ref(v___x_3309_);
lean_dec(v_a_3304_);
return v___x_3379_;
}
}
else
{
lean_dec_ref(v___x_3372_);
lean_dec_ref(v___x_3369_);
lean_dec_ref(v___x_3309_);
lean_dec(v_a_3304_);
return v___x_3377_;
}
}
else
{
lean_dec_ref(v___x_3372_);
lean_dec_ref(v___x_3369_);
lean_dec_ref(v___x_3365_);
lean_dec_ref(v___x_3309_);
lean_dec(v_a_3304_);
return v___x_3374_;
}
}
else
{
lean_dec_ref(v___f_3348_);
lean_dec_ref(v___x_3309_);
lean_dec(v_a_3304_);
lean_dec_ref(v_diseqs_3299_);
lean_dec_ref(v_uppers_3298_);
lean_dec_ref(v_lowers_3297_);
lean_dec_ref(v_dvds_3296_);
return v___x_3360_;
}
}
}
v___jp_3310_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
v___x_3324_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1));
lean_inc(v___y_3311_);
v___x_3325_ = l_Lean_Name_append(v___x_3324_, v___y_3311_);
v___x_3326_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3322_, v_options_3321_, v___x_3325_);
lean_dec(v___x_3325_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; 
lean_dec(v___y_3311_);
lean_dec_ref(v___x_3309_);
v___x_3327_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3323_);
return v___x_3327_;
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3328_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3);
v___x_3329_ = lean_array_to_list(v___x_3309_);
v___x_3330_ = lean_box(0);
v___x_3331_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(v___x_3329_, v___x_3330_);
v___x_3332_ = l_Lean_MessageData_ofList(v___x_3331_);
v___x_3333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3328_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v___x_3334_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___y_3311_, v___x_3333_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3323_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v___x_3335_; 
lean_dec_ref_known(v___x_3334_, 1);
v___x_3335_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3323_);
return v___x_3335_;
}
else
{
return v___x_3334_;
}
}
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec(v_a_3302_);
lean_dec_ref(v_diseqs_3299_);
lean_dec_ref(v_uppers_3298_);
lean_dec_ref(v_lowers_3297_);
lean_dec_ref(v_dvds_3296_);
lean_dec_ref(v_varsHistory_3295_);
lean_dec_ref(v_vars_3294_);
v_a_3410_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3303_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3303_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec_ref(v_diseqs_3299_);
lean_dec_ref(v_uppers_3298_);
lean_dec_ref(v_lowers_3297_);
lean_dec_ref(v_dvds_3296_);
lean_dec_ref(v_varsHistory_3295_);
lean_dec_ref(v_vars_3294_);
v_a_3418_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3301_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3301_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3428_; 
lean_dec_ref(v_diseqs_3299_);
lean_dec_ref(v_uppers_3298_);
lean_dec_ref(v_lowers_3297_);
lean_dec_ref(v_dvds_3296_);
lean_dec_ref(v_varsHistory_3295_);
lean_dec_ref(v_vars_3294_);
v___x_3426_ = lean_box(0);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3426_);
v___x_3428_ = v___x_3292_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
v_a_3431_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3289_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3289_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_);
lean_dec(v_a_3448_);
lean_dec_ref(v_a_3447_);
lean_dec(v_a_3446_);
lean_dec_ref(v_a_3445_);
lean_dec(v_a_3444_);
lean_dec_ref(v_a_3443_);
lean_dec(v_a_3442_);
lean_dec_ref(v_a_3441_);
lean_dec(v_a_3440_);
lean_dec(v_a_3439_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object* v_00_u03b2_3451_, lean_object* v_00_u03c3_3452_, lean_object* v_pm_3453_, lean_object* v_f_3454_){
_start:
{
lean_object* v___x_3455_; 
v___x_3455_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(v_pm_3453_, v_f_3454_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(lean_object* v_cls_3456_, lean_object* v_msg_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v_cls_3456_, v_msg_3457_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___boxed(lean_object* v_cls_3470_, lean_object* v_msg_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(v_cls_3470_, v_msg_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec(v___y_3472_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___redArg(lean_object* v_pm_3484_, lean_object* v_f_3485_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v_f_3485_, v_pm_3484_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1(lean_object* v_00_u03b2_3487_, lean_object* v_00_u03c3_3488_, lean_object* v_pm_3489_, lean_object* v_f_3490_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v_f_3490_, v_pm_3489_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_3492_, lean_object* v_00_u03b2_3493_, lean_object* v_00_u03c3_3494_, lean_object* v_f_3495_, lean_object* v_n_3496_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v_f_3495_, v_n_3496_);
return v___x_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21(lean_object* v_00_u03b1_3498_, lean_object* v_00_u03b2_3499_, lean_object* v_00_u03c3_3500_, lean_object* v_f_3501_, size_t v_sz_3502_, size_t v_i_3503_, lean_object* v_bs_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(v_f_3501_, v_sz_3502_, v_i_3503_, v_bs_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___boxed(lean_object* v_00_u03b1_3506_, lean_object* v_00_u03b2_3507_, lean_object* v_00_u03c3_3508_, lean_object* v_f_3509_, lean_object* v_sz_3510_, lean_object* v_i_3511_, lean_object* v_bs_3512_){
_start:
{
size_t v_sz_boxed_3513_; size_t v_i_boxed_3514_; lean_object* v_res_3515_; 
v_sz_boxed_3513_ = lean_unbox_usize(v_sz_3510_);
lean_dec(v_sz_3510_);
v_i_boxed_3514_ = lean_unbox_usize(v_i_3511_);
lean_dec(v_i_3511_);
v_res_3515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21(v_00_u03b1_3506_, v_00_u03b2_3507_, v_00_u03c3_3508_, v_f_3509_, v_sz_boxed_3513_, v_i_boxed_3514_, v_bs_3512_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22(lean_object* v_00_u03b1_3516_, lean_object* v_00_u03b2_3517_, lean_object* v_f_3518_, lean_object* v_as_3519_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(v_f_3518_, v_as_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___boxed(lean_object* v_00_u03b1_3521_, lean_object* v_00_u03b2_3522_, lean_object* v_f_3523_, lean_object* v_as_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22(v_00_u03b1_3521_, v_00_u03b2_3522_, v_f_3523_, v_as_3524_);
lean_dec_ref(v_as_3524_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42(lean_object* v_00_u03b1_3526_, lean_object* v_00_u03b2_3527_, lean_object* v_f_3528_, lean_object* v_as_3529_, lean_object* v_i_3530_, lean_object* v_acc_3531_, lean_object* v_hle_3532_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(v_f_3528_, v_as_3529_, v_i_3530_, v_acc_3531_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___boxed(lean_object* v_00_u03b1_3534_, lean_object* v_00_u03b2_3535_, lean_object* v_f_3536_, lean_object* v_as_3537_, lean_object* v_i_3538_, lean_object* v_acc_3539_, lean_object* v_hle_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42(v_00_u03b1_3534_, v_00_u03b2_3535_, v_f_3536_, v_as_3537_, v_i_3538_, v_acc_3539_, v_hle_3540_);
lean_dec_ref(v_as_3537_);
return v_res_3541_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(builtin);
}
#ifdef __cplusplus
}
#endif
