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
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
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
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(lean_object* v_a_5_, lean_object* v_x_6_, lean_object* v_a_7_){
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
lean_object* v_v_16_; lean_object* v_maxLowerCoeff_17_; lean_object* v_xs_x27_18_; lean_object* v___y_20_; uint8_t v___x_32_; 
v_v_16_ = lean_array_fget(v_a_7_, v_x_6_);
v_maxLowerCoeff_17_ = lean_ctor_get(v_v_16_, 0);
v_xs_x27_18_ = lean_array_fset(v_a_7_, v_x_6_, v___x_9_);
v___x_32_ = lean_nat_dec_le(v_a_5_, v_maxLowerCoeff_17_);
if (v___x_32_ == 0)
{
v___y_20_ = v_a_5_;
goto v___jp_19_;
}
else
{
lean_dec(v_a_5_);
lean_inc(v_maxLowerCoeff_17_);
v___y_20_ = v_maxLowerCoeff_17_;
goto v___jp_19_;
}
v___jp_19_:
{
lean_object* v_maxUpperCoeff_21_; lean_object* v_maxDvdCoeff_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_30_; 
v_maxUpperCoeff_21_ = lean_ctor_get(v_v_16_, 1);
v_maxDvdCoeff_22_ = lean_ctor_get(v_v_16_, 2);
v_isSharedCheck_30_ = !lean_is_exclusive(v_v_16_);
if (v_isSharedCheck_30_ == 0)
{
lean_object* v_unused_31_; 
v_unused_31_ = lean_ctor_get(v_v_16_, 0);
lean_dec(v_unused_31_);
v___x_24_ = v_v_16_;
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_maxDvdCoeff_22_);
lean_inc(v_maxUpperCoeff_21_);
lean_dec(v_v_16_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___y_20_);
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___y_20_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_maxUpperCoeff_21_);
lean_ctor_set(v_reuseFailAlloc_29_, 2, v_maxDvdCoeff_22_);
v___x_27_ = v_reuseFailAlloc_29_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; 
v___x_28_ = lean_array_fset(v_xs_x27_18_, v_x_6_, v___x_27_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5_ = stack[0].m_obj;
lean_object* v_x_6_ = stack[1].m_obj;
lean_object* v_a_7_ = stack[2].m_obj;
lean_object* v_res_33_;
v_res_33_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_5_, v_x_6_, v_a_7_);
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg___boxed(lean_object* v_a_34_, lean_object* v_x_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_34_, v_x_35_, v_a_36_);
lean_dec(v_x_35_);
return v_res_38_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(lean_object* v_a_39_, lean_object* v_x_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_39_, v_x_40_, v_a_41_);
return v___x_53_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_39_ = stack[0].m_obj;
lean_object* v_x_40_ = stack[1].m_obj;
lean_object* v_a_41_ = stack[2].m_obj;
lean_object* v_a_42_ = stack[3].m_obj;
lean_object* v_a_43_ = stack[4].m_obj;
lean_object* v_a_44_ = stack[5].m_obj;
lean_object* v_a_45_ = stack[6].m_obj;
lean_object* v_a_46_ = stack[7].m_obj;
lean_object* v_a_47_ = stack[8].m_obj;
lean_object* v_a_48_ = stack[9].m_obj;
lean_object* v_a_49_ = stack[10].m_obj;
lean_object* v_a_50_ = stack[11].m_obj;
lean_object* v_a_51_ = stack[12].m_obj;
lean_object* v_res_54_;
v_res_54_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(v_a_39_, v_x_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___boxed(lean_object* v_a_55_, lean_object* v_x_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(v_a_55_, v_x_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
lean_dec(v_a_58_);
lean_dec(v_x_56_);
return v_res_69_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(lean_object* v_a_70_, lean_object* v_x_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_74_; lean_object* v___y_76_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_74_ = lean_box(0);
v___x_79_ = lean_array_get_size(v_a_72_);
v___x_80_ = lean_nat_dec_lt(v_x_71_, v___x_79_);
if (v___x_80_ == 0)
{
lean_dec(v_a_70_);
v___y_76_ = v_a_72_;
goto v___jp_75_;
}
else
{
lean_object* v_v_81_; lean_object* v_maxLowerCoeff_82_; lean_object* v_maxUpperCoeff_83_; lean_object* v_maxDvdCoeff_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_96_; 
v_v_81_ = lean_array_fget(v_a_72_, v_x_71_);
v_maxLowerCoeff_82_ = lean_ctor_get(v_v_81_, 0);
v_maxUpperCoeff_83_ = lean_ctor_get(v_v_81_, 1);
v_maxDvdCoeff_84_ = lean_ctor_get(v_v_81_, 2);
v_isSharedCheck_96_ = !lean_is_exclusive(v_v_81_);
if (v_isSharedCheck_96_ == 0)
{
v___x_86_ = v_v_81_;
v_isShared_87_ = v_isSharedCheck_96_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_maxDvdCoeff_84_);
lean_inc(v_maxUpperCoeff_83_);
lean_inc(v_maxLowerCoeff_82_);
lean_dec(v_v_81_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_96_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v_xs_x27_88_; lean_object* v___y_90_; uint8_t v___x_95_; 
v_xs_x27_88_ = lean_array_fset(v_a_72_, v_x_71_, v___x_74_);
v___x_95_ = lean_nat_dec_le(v_a_70_, v_maxUpperCoeff_83_);
if (v___x_95_ == 0)
{
lean_dec(v_maxUpperCoeff_83_);
v___y_90_ = v_a_70_;
goto v___jp_89_;
}
else
{
lean_dec(v_a_70_);
v___y_90_ = v_maxUpperCoeff_83_;
goto v___jp_89_;
}
v___jp_89_:
{
lean_object* v___x_92_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v___y_90_);
v___x_92_ = v___x_86_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_maxLowerCoeff_82_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___y_90_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v_maxDvdCoeff_84_);
v___x_92_ = v_reuseFailAlloc_94_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; 
v___x_93_ = lean_array_fset(v_xs_x27_88_, v_x_71_, v___x_92_);
v___y_76_ = v___x_93_;
goto v___jp_75_;
}
}
}
}
v___jp_75_:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_74_);
lean_ctor_set(v___x_77_, 1, v___y_76_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_70_ = stack[0].m_obj;
lean_object* v_x_71_ = stack[1].m_obj;
lean_object* v_a_72_ = stack[2].m_obj;
lean_object* v_res_97_;
v_res_97_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_70_, v_x_71_, v_a_72_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg___boxed(lean_object* v_a_98_, lean_object* v_x_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_98_, v_x_99_, v_a_100_);
lean_dec(v_x_99_);
return v_res_102_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(lean_object* v_a_103_, lean_object* v_x_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_103_, v_x_104_, v_a_105_);
return v___x_117_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_103_ = stack[0].m_obj;
lean_object* v_x_104_ = stack[1].m_obj;
lean_object* v_a_105_ = stack[2].m_obj;
lean_object* v_a_106_ = stack[3].m_obj;
lean_object* v_a_107_ = stack[4].m_obj;
lean_object* v_a_108_ = stack[5].m_obj;
lean_object* v_a_109_ = stack[6].m_obj;
lean_object* v_a_110_ = stack[7].m_obj;
lean_object* v_a_111_ = stack[8].m_obj;
lean_object* v_a_112_ = stack[9].m_obj;
lean_object* v_a_113_ = stack[10].m_obj;
lean_object* v_a_114_ = stack[11].m_obj;
lean_object* v_a_115_ = stack[12].m_obj;
lean_object* v_res_118_;
v_res_118_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(v_a_103_, v_x_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___boxed(lean_object* v_a_119_, lean_object* v_x_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(v_a_119_, v_x_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec(v_a_122_);
lean_dec(v_x_120_);
return v_res_133_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_nat_to_int(v___x_134_);
return v___x_135_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(lean_object* v_a_136_, lean_object* v_x_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0);
v___x_141_ = lean_int_dec_lt(v_a_136_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_nat_abs(v_a_136_);
v___x_143_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v___x_142_, v_x_137_, v_a_138_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_nat_abs(v_a_136_);
v___x_145_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v___x_144_, v_x_137_, v_a_138_);
return v___x_145_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_136_ = stack[0].m_obj;
lean_object* v_x_137_ = stack[1].m_obj;
lean_object* v_a_138_ = stack[2].m_obj;
lean_object* v_res_146_;
v_res_146_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_136_, v_x_137_, v_a_138_);
stack->m_obj
 = v_res_146_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___boxed(lean_object* v_a_147_, lean_object* v_x_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_147_, v_x_148_, v_a_149_);
lean_dec(v_x_148_);
lean_dec(v_a_147_);
return v_res_151_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(lean_object* v_a_152_, lean_object* v_x_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_152_, v_x_153_, v_a_154_);
return v___x_166_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_152_ = stack[0].m_obj;
lean_object* v_x_153_ = stack[1].m_obj;
lean_object* v_a_154_ = stack[2].m_obj;
lean_object* v_a_155_ = stack[3].m_obj;
lean_object* v_a_156_ = stack[4].m_obj;
lean_object* v_a_157_ = stack[5].m_obj;
lean_object* v_a_158_ = stack[6].m_obj;
lean_object* v_a_159_ = stack[7].m_obj;
lean_object* v_a_160_ = stack[8].m_obj;
lean_object* v_a_161_ = stack[9].m_obj;
lean_object* v_a_162_ = stack[10].m_obj;
lean_object* v_a_163_ = stack[11].m_obj;
lean_object* v_a_164_ = stack[12].m_obj;
lean_object* v_res_167_;
v_res_167_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(v_a_152_, v_x_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___boxed(lean_object* v_a_168_, lean_object* v_x_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(v_a_168_, v_x_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec(v_a_171_);
lean_dec(v_x_169_);
lean_dec(v_a_168_);
return v_res_182_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(lean_object* v_a_183_, lean_object* v_x_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_187_; lean_object* v___y_189_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_187_ = lean_box(0);
v___x_192_ = lean_array_get_size(v_a_185_);
v___x_193_ = lean_nat_dec_lt(v_x_184_, v___x_192_);
if (v___x_193_ == 0)
{
lean_dec(v_a_183_);
v___y_189_ = v_a_185_;
goto v___jp_188_;
}
else
{
lean_object* v_v_194_; lean_object* v_maxLowerCoeff_195_; lean_object* v_maxUpperCoeff_196_; lean_object* v_maxDvdCoeff_197_; lean_object* v_xs_x27_198_; uint8_t v___x_199_; 
v_v_194_ = lean_array_fget(v_a_185_, v_x_184_);
v_maxLowerCoeff_195_ = lean_ctor_get(v_v_194_, 0);
v_maxUpperCoeff_196_ = lean_ctor_get(v_v_194_, 1);
v_maxDvdCoeff_197_ = lean_ctor_get(v_v_194_, 2);
v_xs_x27_198_ = lean_array_fset(v_a_185_, v_x_184_, v___x_187_);
v___x_199_ = lean_nat_dec_le(v_a_183_, v_maxDvdCoeff_197_);
if (v___x_199_ == 0)
{
lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_207_; 
lean_inc(v_maxUpperCoeff_196_);
lean_inc(v_maxLowerCoeff_195_);
v_isSharedCheck_207_ = !lean_is_exclusive(v_v_194_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; lean_object* v_unused_209_; lean_object* v_unused_210_; 
v_unused_208_ = lean_ctor_get(v_v_194_, 2);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_v_194_, 1);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_v_194_, 0);
lean_dec(v_unused_210_);
v___x_201_ = v_v_194_;
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
else
{
lean_dec(v_v_194_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 2, v_a_183_);
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_maxLowerCoeff_195_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_maxUpperCoeff_196_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_a_183_);
v___x_204_ = v_reuseFailAlloc_206_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; 
v___x_205_ = lean_array_fset(v_xs_x27_198_, v_x_184_, v___x_204_);
v___y_189_ = v___x_205_;
goto v___jp_188_;
}
}
}
else
{
lean_object* v___x_211_; 
lean_dec(v_a_183_);
v___x_211_ = lean_array_fset(v_xs_x27_198_, v_x_184_, v_v_194_);
v___y_189_ = v___x_211_;
goto v___jp_188_;
}
}
v___jp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_187_);
lean_ctor_set(v___x_190_, 1, v___y_189_);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_183_ = stack[0].m_obj;
lean_object* v_x_184_ = stack[1].m_obj;
lean_object* v_a_185_ = stack[2].m_obj;
lean_object* v_res_212_;
v_res_212_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_183_, v_x_184_, v_a_185_);
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg___boxed(lean_object* v_a_213_, lean_object* v_x_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_213_, v_x_214_, v_a_215_);
lean_dec(v_x_214_);
return v_res_217_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(lean_object* v_a_218_, lean_object* v_x_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_218_, v_x_219_, v_a_220_);
return v___x_232_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_218_ = stack[0].m_obj;
lean_object* v_x_219_ = stack[1].m_obj;
lean_object* v_a_220_ = stack[2].m_obj;
lean_object* v_a_221_ = stack[3].m_obj;
lean_object* v_a_222_ = stack[4].m_obj;
lean_object* v_a_223_ = stack[5].m_obj;
lean_object* v_a_224_ = stack[6].m_obj;
lean_object* v_a_225_ = stack[7].m_obj;
lean_object* v_a_226_ = stack[8].m_obj;
lean_object* v_a_227_ = stack[9].m_obj;
lean_object* v_a_228_ = stack[10].m_obj;
lean_object* v_a_229_ = stack[11].m_obj;
lean_object* v_a_230_ = stack[12].m_obj;
lean_object* v_res_233_;
v_res_233_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(v_a_218_, v_x_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
stack->m_obj
 = v_res_233_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___boxed(lean_object* v_a_234_, lean_object* v_x_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(v_a_234_, v_x_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec(v_a_237_);
lean_dec(v_x_235_);
return v_res_248_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
if (lean_obj_tag(v_a_249_) == 0)
{
lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_260_; 
v_isSharedCheck_260_ = !lean_is_exclusive(v_a_249_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; 
v_unused_261_ = lean_ctor_get(v_a_249_, 0);
lean_dec(v_unused_261_);
v___x_253_ = v_a_249_;
v_isShared_254_ = v_isSharedCheck_260_;
goto v_resetjp_252_;
}
else
{
lean_dec(v_a_249_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_260_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v_a_250_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_256_);
v___x_258_ = v___x_253_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_k_262_; lean_object* v_v_263_; lean_object* v_p_264_; lean_object* v___x_265_; lean_object* v_a_266_; lean_object* v_snd_267_; 
v_k_262_ = lean_ctor_get(v_a_249_, 0);
lean_inc(v_k_262_);
v_v_263_ = lean_ctor_get(v_a_249_, 1);
lean_inc(v_v_263_);
v_p_264_ = lean_ctor_get(v_a_249_, 2);
lean_inc_ref(v_p_264_);
lean_dec_ref_known(v_a_249_, 3);
v___x_265_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_k_262_, v_v_263_, v_a_250_);
lean_dec(v_v_263_);
lean_dec(v_k_262_);
v_a_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_266_);
lean_dec_ref(v___x_265_);
v_snd_267_ = lean_ctor_get(v_a_266_, 1);
lean_inc(v_snd_267_);
lean_dec(v_a_266_);
v_a_249_ = v_p_264_;
v_a_250_ = v_snd_267_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_249_ = stack[0].m_obj;
lean_object* v_a_250_ = stack[1].m_obj;
lean_object* v_res_269_;
v_res_269_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_249_, v_a_250_);
stack->m_obj
 = v_res_269_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg___boxed(lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_270_, v_a_271_);
return v_res_273_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_274_, v_a_275_);
return v___x_287_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_274_ = stack[0].m_obj;
lean_object* v_a_275_ = stack[1].m_obj;
lean_object* v_a_276_ = stack[2].m_obj;
lean_object* v_a_277_ = stack[3].m_obj;
lean_object* v_a_278_ = stack[4].m_obj;
lean_object* v_a_279_ = stack[5].m_obj;
lean_object* v_a_280_ = stack[6].m_obj;
lean_object* v_a_281_ = stack[7].m_obj;
lean_object* v_a_282_ = stack[8].m_obj;
lean_object* v_a_283_ = stack[9].m_obj;
lean_object* v_a_284_ = stack[10].m_obj;
lean_object* v_a_285_ = stack[11].m_obj;
lean_object* v_res_288_;
v_res_288_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___boxed(lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec(v_a_291_);
return v_res_302_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(lean_object* v_as_306_, size_t v_sz_307_, size_t v_i_308_, lean_object* v_b_309_, lean_object* v___y_310_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = lean_usize_dec_lt(v_i_308_, v_sz_307_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v_b_309_);
lean_ctor_set(v___x_313_, 1, v___y_310_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
else
{
lean_object* v_a_315_; lean_object* v_p_316_; lean_object* v___x_317_; 
lean_dec_ref(v_b_309_);
v_a_315_ = lean_array_uget_borrowed(v_as_306_, v_i_308_);
v_p_316_ = lean_ctor_get(v_a_315_, 0);
lean_inc_ref(v_p_316_);
v___x_317_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_316_, v___y_310_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v_snd_319_; lean_object* v___x_320_; size_t v___x_321_; size_t v___x_322_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
v_snd_319_ = lean_ctor_get(v_a_318_, 1);
lean_inc(v_snd_319_);
lean_dec(v_a_318_);
v___x_320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_add(v_i_308_, v___x_321_);
v_i_308_ = v___x_322_;
v_b_309_ = v___x_320_;
v___y_310_ = v_snd_319_;
goto _start;
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
v_a_324_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_317_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_317_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_306_ = stack[0].m_obj;
size_t v_sz_307_ = stack[1].m_num;
size_t v_i_308_ = stack[2].m_num;
lean_object* v_b_309_ = stack[3].m_obj;
lean_object* v___y_310_ = stack[4].m_obj;
lean_object* v_res_332_;
v_res_332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_306_, v_sz_307_, v_i_308_, v_b_309_, v___y_310_);
stack->m_obj
 = v_res_332_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_333_, lean_object* v_sz_334_, lean_object* v_i_335_, lean_object* v_b_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
size_t v_sz_boxed_339_; size_t v_i_boxed_340_; lean_object* v_res_341_; 
v_sz_boxed_339_ = lean_unbox_usize(v_sz_334_);
lean_dec(v_sz_334_);
v_i_boxed_340_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_res_341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_333_, v_sz_boxed_339_, v_i_boxed_340_, v_b_336_, v___y_337_);
lean_dec_ref(v_as_333_);
return v_res_341_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(lean_object* v_as_342_, size_t v_sz_343_, size_t v_i_344_, lean_object* v_b_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = lean_usize_dec_lt(v_i_344_, v_sz_343_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_b_345_);
lean_ctor_set(v___x_359_, 1, v___y_346_);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
else
{
lean_object* v_a_361_; lean_object* v_p_362_; lean_object* v___x_363_; 
lean_dec_ref(v_b_345_);
v_a_361_ = lean_array_uget_borrowed(v_as_342_, v_i_344_);
v_p_362_ = lean_ctor_get(v_a_361_, 0);
lean_inc_ref(v_p_362_);
v___x_363_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_362_, v___y_346_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v_snd_365_; lean_object* v___x_366_; size_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
v_snd_365_ = lean_ctor_get(v_a_364_, 1);
lean_inc(v_snd_365_);
lean_dec(v_a_364_);
v___x_366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_367_ = ((size_t)1ULL);
v___x_368_ = lean_usize_add(v_i_344_, v___x_367_);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_342_, v_sz_343_, v___x_368_, v___x_366_, v_snd_365_);
return v___x_369_;
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
v_a_370_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_363_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_363_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_342_ = stack[0].m_obj;
size_t v_sz_343_ = stack[1].m_num;
size_t v_i_344_ = stack[2].m_num;
lean_object* v_b_345_ = stack[3].m_obj;
lean_object* v___y_346_ = stack[4].m_obj;
lean_object* v___y_347_ = stack[5].m_obj;
lean_object* v___y_348_ = stack[6].m_obj;
lean_object* v___y_349_ = stack[7].m_obj;
lean_object* v___y_350_ = stack[8].m_obj;
lean_object* v___y_351_ = stack[9].m_obj;
lean_object* v___y_352_ = stack[10].m_obj;
lean_object* v___y_353_ = stack[11].m_obj;
lean_object* v___y_354_ = stack[12].m_obj;
lean_object* v___y_355_ = stack[13].m_obj;
lean_object* v___y_356_ = stack[14].m_obj;
lean_object* v_res_378_;
v_res_378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_as_342_, v_sz_343_, v_i_344_, v_b_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1___boxed(lean_object* v_as_379_, lean_object* v_sz_380_, lean_object* v_i_381_, lean_object* v_b_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
size_t v_sz_boxed_395_; size_t v_i_boxed_396_; lean_object* v_res_397_; 
v_sz_boxed_395_ = lean_unbox_usize(v_sz_380_);
lean_dec(v_sz_380_);
v_i_boxed_396_ = lean_unbox_usize(v_i_381_);
lean_dec(v_i_381_);
v_res_397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_as_379_, v_sz_boxed_395_, v_i_boxed_396_, v_b_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v_as_379_);
return v_res_397_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_as_401_, size_t v_sz_402_, size_t v_i_403_, lean_object* v_b_404_, lean_object* v___y_405_){
_start:
{
uint8_t v___x_407_; 
v___x_407_ = lean_usize_dec_lt(v_i_403_, v_sz_402_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_b_404_);
lean_ctor_set(v___x_408_, 1, v___y_405_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
else
{
lean_object* v_a_410_; lean_object* v_p_411_; lean_object* v___x_412_; 
lean_dec_ref(v_b_404_);
v_a_410_ = lean_array_uget_borrowed(v_as_401_, v_i_403_);
v_p_411_ = lean_ctor_get(v_a_410_, 0);
lean_inc_ref(v_p_411_);
v___x_412_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_411_, v___y_405_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v_snd_414_; lean_object* v___x_415_; size_t v___x_416_; size_t v___x_417_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v_snd_414_ = lean_ctor_get(v_a_413_, 1);
lean_inc(v_snd_414_);
lean_dec(v_a_413_);
v___x_415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_add(v_i_403_, v___x_416_);
v_i_403_ = v___x_417_;
v_b_404_ = v___x_415_;
v___y_405_ = v_snd_414_;
goto _start;
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
v_a_419_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_412_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_412_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_401_ = stack[0].m_obj;
size_t v_sz_402_ = stack[1].m_num;
size_t v_i_403_ = stack[2].m_num;
lean_object* v_b_404_ = stack[3].m_obj;
lean_object* v___y_405_ = stack[4].m_obj;
lean_object* v_res_427_;
v_res_427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_401_, v_sz_402_, v_i_403_, v_b_404_, v___y_405_);
stack->m_obj
 = v_res_427_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_as_428_, lean_object* v_sz_429_, lean_object* v_i_430_, lean_object* v_b_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
size_t v_sz_boxed_434_; size_t v_i_boxed_435_; lean_object* v_res_436_; 
v_sz_boxed_434_ = lean_unbox_usize(v_sz_429_);
lean_dec(v_sz_429_);
v_i_boxed_435_ = lean_unbox_usize(v_i_430_);
lean_dec(v_i_430_);
v_res_436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_428_, v_sz_boxed_434_, v_i_boxed_435_, v_b_431_, v___y_432_);
lean_dec_ref(v_as_428_);
return v_res_436_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(lean_object* v_as_437_, size_t v_sz_438_, size_t v_i_439_, lean_object* v_b_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = lean_usize_dec_lt(v_i_439_, v_sz_438_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v_b_440_);
lean_ctor_set(v___x_454_, 1, v___y_441_);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
else
{
lean_object* v_a_456_; lean_object* v_p_457_; lean_object* v___x_458_; 
lean_dec_ref(v_b_440_);
v_a_456_ = lean_array_uget_borrowed(v_as_437_, v_i_439_);
v_p_457_ = lean_ctor_get(v_a_456_, 0);
lean_inc_ref(v_p_457_);
v___x_458_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_457_, v___y_441_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v_snd_460_; lean_object* v___x_461_; size_t v___x_462_; size_t v___x_463_; lean_object* v___x_464_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
v_snd_460_ = lean_ctor_get(v_a_459_, 1);
lean_inc(v_snd_460_);
lean_dec(v_a_459_);
v___x_461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_add(v_i_439_, v___x_462_);
v___x_464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_437_, v_sz_438_, v___x_463_, v___x_461_, v_snd_460_);
return v___x_464_;
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v_a_465_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_458_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_458_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_437_ = stack[0].m_obj;
size_t v_sz_438_ = stack[1].m_num;
size_t v_i_439_ = stack[2].m_num;
lean_object* v_b_440_ = stack[3].m_obj;
lean_object* v___y_441_ = stack[4].m_obj;
lean_object* v___y_442_ = stack[5].m_obj;
lean_object* v___y_443_ = stack[6].m_obj;
lean_object* v___y_444_ = stack[7].m_obj;
lean_object* v___y_445_ = stack[8].m_obj;
lean_object* v___y_446_ = stack[9].m_obj;
lean_object* v___y_447_ = stack[10].m_obj;
lean_object* v___y_448_ = stack[11].m_obj;
lean_object* v___y_449_ = stack[12].m_obj;
lean_object* v___y_450_ = stack[13].m_obj;
lean_object* v___y_451_ = stack[14].m_obj;
lean_object* v_res_473_;
v_res_473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_as_437_, v_sz_438_, v_i_439_, v_b_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
stack->m_obj
 = v_res_473_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2___boxed(lean_object* v_as_474_, lean_object* v_sz_475_, lean_object* v_i_476_, lean_object* v_b_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
size_t v_sz_boxed_490_; size_t v_i_boxed_491_; lean_object* v_res_492_; 
v_sz_boxed_490_ = lean_unbox_usize(v_sz_475_);
lean_dec(v_sz_475_);
v_i_boxed_491_ = lean_unbox_usize(v_i_476_);
lean_dec(v_i_476_);
v_res_492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_as_474_, v_sz_boxed_490_, v_i_boxed_491_, v_b_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v_as_474_);
return v_res_492_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(lean_object* v_init_493_, lean_object* v_n_494_, lean_object* v_b_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
if (lean_obj_tag(v_n_494_) == 0)
{
lean_object* v_cs_508_; lean_object* v___x_509_; lean_object* v___x_510_; size_t v_sz_511_; size_t v___x_512_; lean_object* v___x_513_; 
v_cs_508_ = lean_ctor_get(v_n_494_, 0);
v___x_509_ = lean_box(0);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v_b_495_);
v_sz_511_ = lean_array_size(v_cs_508_);
v___x_512_ = ((size_t)0ULL);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_493_, v_cs_508_, v_sz_511_, v___x_512_, v___x_510_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_548_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_548_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_548_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_548_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_fst_518_; lean_object* v_fst_519_; 
v_fst_518_ = lean_ctor_get(v_a_514_, 0);
lean_inc(v_fst_518_);
v_fst_519_ = lean_ctor_get(v_fst_518_, 0);
if (lean_obj_tag(v_fst_519_) == 0)
{
lean_object* v_snd_520_; lean_object* v_snd_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_532_; 
v_snd_520_ = lean_ctor_get(v_a_514_, 1);
lean_inc(v_snd_520_);
lean_dec(v_a_514_);
v_snd_521_ = lean_ctor_get(v_fst_518_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v_fst_518_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v_fst_518_, 0);
lean_dec(v_unused_533_);
v___x_523_ = v_fst_518_;
v_isShared_524_ = v_isSharedCheck_532_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_snd_521_);
lean_dec(v_fst_518_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_532_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v_snd_521_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v_snd_520_);
lean_ctor_set(v___x_523_, 0, v___x_525_);
v___x_527_ = v___x_523_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_snd_520_);
v___x_527_ = v_reuseFailAlloc_531_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_529_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_527_);
v___x_529_ = v___x_516_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_545_; 
lean_inc_ref(v_fst_519_);
v_isSharedCheck_545_ = !lean_is_exclusive(v_fst_518_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; lean_object* v_unused_547_; 
v_unused_546_ = lean_ctor_get(v_fst_518_, 1);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_fst_518_, 0);
lean_dec(v_unused_547_);
v___x_535_ = v_fst_518_;
v_isShared_536_ = v_isSharedCheck_545_;
goto v_resetjp_534_;
}
else
{
lean_dec(v_fst_518_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_545_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v_snd_537_; lean_object* v_val_538_; lean_object* v___x_540_; 
v_snd_537_ = lean_ctor_get(v_a_514_, 1);
lean_inc(v_snd_537_);
lean_dec(v_a_514_);
v_val_538_ = lean_ctor_get(v_fst_519_, 0);
lean_inc(v_val_538_);
lean_dec_ref_known(v_fst_519_, 1);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v_snd_537_);
lean_ctor_set(v___x_535_, 0, v_val_538_);
v___x_540_ = v___x_535_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_val_538_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_snd_537_);
v___x_540_ = v_reuseFailAlloc_544_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_540_);
v___x_542_ = v___x_516_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
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
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v_a_549_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_513_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_513_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v_vs_557_; lean_object* v___x_558_; lean_object* v___x_559_; size_t v_sz_560_; size_t v___x_561_; lean_object* v___x_562_; 
v_vs_557_ = lean_ctor_get(v_n_494_, 0);
v___x_558_ = lean_box(0);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v_b_495_);
v_sz_560_ = lean_array_size(v_vs_557_);
v___x_561_ = ((size_t)0ULL);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_vs_557_, v_sz_560_, v___x_561_, v___x_559_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_597_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_597_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_597_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_597_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v_fst_567_; lean_object* v_fst_568_; 
v_fst_567_ = lean_ctor_get(v_a_563_, 0);
lean_inc(v_fst_567_);
v_fst_568_ = lean_ctor_get(v_fst_567_, 0);
if (lean_obj_tag(v_fst_568_) == 0)
{
lean_object* v_snd_569_; lean_object* v_snd_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_581_; 
v_snd_569_ = lean_ctor_get(v_a_563_, 1);
lean_inc(v_snd_569_);
lean_dec(v_a_563_);
v_snd_570_ = lean_ctor_get(v_fst_567_, 1);
v_isSharedCheck_581_ = !lean_is_exclusive(v_fst_567_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_fst_567_, 0);
lean_dec(v_unused_582_);
v___x_572_ = v_fst_567_;
v_isShared_573_ = v_isSharedCheck_581_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_snd_570_);
lean_dec(v_fst_567_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_581_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_574_, 0, v_snd_570_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v_snd_569_);
lean_ctor_set(v___x_572_, 0, v___x_574_);
v___x_576_ = v___x_572_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_snd_569_);
v___x_576_ = v_reuseFailAlloc_580_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_578_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_576_);
v___x_578_ = v___x_565_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_594_; 
lean_inc_ref(v_fst_568_);
v_isSharedCheck_594_ = !lean_is_exclusive(v_fst_567_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; lean_object* v_unused_596_; 
v_unused_595_ = lean_ctor_get(v_fst_567_, 1);
lean_dec(v_unused_595_);
v_unused_596_ = lean_ctor_get(v_fst_567_, 0);
lean_dec(v_unused_596_);
v___x_584_ = v_fst_567_;
v_isShared_585_ = v_isSharedCheck_594_;
goto v_resetjp_583_;
}
else
{
lean_dec(v_fst_567_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_594_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v_snd_586_; lean_object* v_val_587_; lean_object* v___x_589_; 
v_snd_586_ = lean_ctor_get(v_a_563_, 1);
lean_inc(v_snd_586_);
lean_dec(v_a_563_);
v_val_587_ = lean_ctor_get(v_fst_568_, 0);
lean_inc(v_val_587_);
lean_dec_ref_known(v_fst_568_, 1);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 1, v_snd_586_);
lean_ctor_set(v___x_584_, 0, v_val_587_);
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_val_587_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_snd_586_);
v___x_589_ = v_reuseFailAlloc_593_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_591_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_589_);
v___x_591_ = v___x_565_;
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
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_a_598_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_562_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_562_);
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
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_493_ = stack[0].m_obj;
lean_object* v_n_494_ = stack[1].m_obj;
lean_object* v_b_495_ = stack[2].m_obj;
lean_object* v___y_496_ = stack[3].m_obj;
lean_object* v___y_497_ = stack[4].m_obj;
lean_object* v___y_498_ = stack[5].m_obj;
lean_object* v___y_499_ = stack[6].m_obj;
lean_object* v___y_500_ = stack[7].m_obj;
lean_object* v___y_501_ = stack[8].m_obj;
lean_object* v___y_502_ = stack[9].m_obj;
lean_object* v___y_503_ = stack[10].m_obj;
lean_object* v___y_504_ = stack[11].m_obj;
lean_object* v___y_505_ = stack[12].m_obj;
lean_object* v___y_506_ = stack[13].m_obj;
lean_object* v_res_606_;
v_res_606_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_493_, v_n_494_, v_b_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
stack->m_obj
 = v_res_606_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(lean_object* v_init_607_, lean_object* v_as_608_, size_t v_sz_609_, size_t v_i_610_, lean_object* v_b_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_624_; 
v___x_624_ = lean_usize_dec_lt(v_i_610_, v_sz_609_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_b_611_);
lean_ctor_set(v___x_625_, 1, v___y_612_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
else
{
lean_object* v_snd_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_677_; 
v_snd_627_ = lean_ctor_get(v_b_611_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v_b_611_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v_b_611_, 0);
lean_dec(v_unused_678_);
v___x_629_ = v_b_611_;
v_isShared_630_ = v_isSharedCheck_677_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_snd_627_);
lean_dec(v_b_611_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_677_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v_a_632_; lean_object* v___x_633_; 
v___x_631_ = lean_box(0);
v_a_632_ = lean_array_uget_borrowed(v_as_608_, v_i_610_);
lean_inc(v_snd_627_);
v___x_633_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_607_, v_a_632_, v_snd_627_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_668_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_668_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_668_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_668_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_fst_638_; 
v_fst_638_ = lean_ctor_get(v_a_634_, 0);
lean_inc(v_fst_638_);
if (lean_obj_tag(v_fst_638_) == 0)
{
lean_object* v_snd_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_653_; 
v_snd_639_ = lean_ctor_get(v_a_634_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_a_634_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v_a_634_, 0);
lean_dec(v_unused_654_);
v___x_641_ = v_a_634_;
v_isShared_642_ = v_isSharedCheck_653_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_snd_639_);
lean_dec(v_a_634_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_653_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v_fst_638_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v_snd_627_);
lean_ctor_set(v___x_641_, 0, v___x_643_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_snd_627_);
v___x_645_ = v_reuseFailAlloc_652_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_647_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v_snd_639_);
lean_ctor_set(v___x_629_, 0, v___x_645_);
v___x_647_ = v___x_629_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_snd_639_);
v___x_647_ = v_reuseFailAlloc_651_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_647_);
v___x_649_ = v___x_636_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
else
{
lean_object* v_snd_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_666_; 
lean_del_object(v___x_636_);
lean_del_object(v___x_629_);
lean_dec(v_snd_627_);
v_snd_655_ = lean_ctor_get(v_a_634_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_a_634_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v_a_634_, 0);
lean_dec(v_unused_667_);
v___x_657_ = v_a_634_;
v_isShared_658_ = v_isSharedCheck_666_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snd_655_);
lean_dec(v_a_634_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_666_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_a_659_; lean_object* v___x_661_; 
v_a_659_ = lean_ctor_get(v_fst_638_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v_fst_638_, 1);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v_a_659_);
lean_ctor_set(v___x_657_, 0, v___x_631_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_a_659_);
v___x_661_ = v_reuseFailAlloc_665_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
size_t v___x_662_; size_t v___x_663_; 
v___x_662_ = ((size_t)1ULL);
v___x_663_ = lean_usize_add(v_i_610_, v___x_662_);
v_i_610_ = v___x_663_;
v_b_611_ = v___x_661_;
v___y_612_ = v_snd_655_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_del_object(v___x_629_);
lean_dec(v_snd_627_);
v_a_669_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_633_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_633_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_607_ = stack[0].m_obj;
lean_object* v_as_608_ = stack[1].m_obj;
size_t v_sz_609_ = stack[2].m_num;
size_t v_i_610_ = stack[3].m_num;
lean_object* v_b_611_ = stack[4].m_obj;
lean_object* v___y_612_ = stack[5].m_obj;
lean_object* v___y_613_ = stack[6].m_obj;
lean_object* v___y_614_ = stack[7].m_obj;
lean_object* v___y_615_ = stack[8].m_obj;
lean_object* v___y_616_ = stack[9].m_obj;
lean_object* v___y_617_ = stack[10].m_obj;
lean_object* v___y_618_ = stack[11].m_obj;
lean_object* v___y_619_ = stack[12].m_obj;
lean_object* v___y_620_ = stack[13].m_obj;
lean_object* v___y_621_ = stack[14].m_obj;
lean_object* v___y_622_ = stack[15].m_obj;
lean_object* v_res_679_;
v_res_679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_607_, v_as_608_, v_sz_609_, v_i_610_, v_b_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
stack->m_obj
 = v_res_679_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_680_ = _args[0];
lean_object* v_as_681_ = _args[1];
lean_object* v_sz_682_ = _args[2];
lean_object* v_i_683_ = _args[3];
lean_object* v_b_684_ = _args[4];
lean_object* v___y_685_ = _args[5];
lean_object* v___y_686_ = _args[6];
lean_object* v___y_687_ = _args[7];
lean_object* v___y_688_ = _args[8];
lean_object* v___y_689_ = _args[9];
lean_object* v___y_690_ = _args[10];
lean_object* v___y_691_ = _args[11];
lean_object* v___y_692_ = _args[12];
lean_object* v___y_693_ = _args[13];
lean_object* v___y_694_ = _args[14];
lean_object* v___y_695_ = _args[15];
lean_object* v___y_696_ = _args[16];
_start:
{
size_t v_sz_boxed_697_; size_t v_i_boxed_698_; lean_object* v_res_699_; 
v_sz_boxed_697_ = lean_unbox_usize(v_sz_682_);
lean_dec(v_sz_682_);
v_i_boxed_698_ = lean_unbox_usize(v_i_683_);
lean_dec(v_i_683_);
v_res_699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_680_, v_as_681_, v_sz_boxed_697_, v_i_boxed_698_, v_b_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v_as_681_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0___boxed(lean_object* v_init_700_, lean_object* v_n_701_, lean_object* v_b_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_700_, v_n_701_, v_b_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v_n_701_);
return v_res_715_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(lean_object* v_t_716_, lean_object* v_init_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_b_731_; lean_object* v___y_732_; lean_object* v_root_735_; lean_object* v_tail_736_; lean_object* v___x_737_; 
v_root_735_ = lean_ctor_get(v_t_716_, 0);
v_tail_736_ = lean_ctor_get(v_t_716_, 1);
v___x_737_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_717_, v_root_735_, v_init_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v_fst_739_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
v_fst_739_ = lean_ctor_get(v_a_738_, 0);
lean_inc(v_fst_739_);
if (lean_obj_tag(v_fst_739_) == 0)
{
lean_object* v_snd_740_; lean_object* v_a_741_; 
v_snd_740_ = lean_ctor_get(v_a_738_, 1);
lean_inc(v_snd_740_);
lean_dec(v_a_738_);
v_a_741_ = lean_ctor_get(v_fst_739_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v_fst_739_, 1);
v_b_731_ = v_a_741_;
v___y_732_ = v_snd_740_;
goto v___jp_730_;
}
else
{
lean_object* v_snd_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_784_; 
v_snd_742_ = lean_ctor_get(v_a_738_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_a_738_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v_a_738_, 0);
lean_dec(v_unused_785_);
v___x_744_ = v_a_738_;
v_isShared_745_ = v_isSharedCheck_784_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_snd_742_);
lean_dec(v_a_738_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_784_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_a_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v_a_746_ = lean_ctor_get(v_fst_739_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v_fst_739_, 1);
v___x_747_ = lean_box(0);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v_a_746_);
lean_ctor_set(v___x_744_, 0, v___x_747_);
v___x_749_ = v___x_744_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_a_746_);
v___x_749_ = v_reuseFailAlloc_783_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
size_t v_sz_750_; size_t v___x_751_; lean_object* v___x_752_; 
v_sz_750_ = lean_array_size(v_tail_736_);
v___x_751_ = ((size_t)0ULL);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_tail_736_, v_sz_750_, v___x_751_, v___x_749_, v_snd_742_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_774_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_774_ == 0)
{
v___x_755_ = v___x_752_;
v_isShared_756_ = v_isSharedCheck_774_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_774_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_fst_757_; lean_object* v_fst_758_; 
v_fst_757_ = lean_ctor_get(v_a_753_, 0);
lean_inc(v_fst_757_);
v_fst_758_ = lean_ctor_get(v_fst_757_, 0);
if (lean_obj_tag(v_fst_758_) == 0)
{
lean_object* v_snd_759_; lean_object* v_snd_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_770_; 
v_snd_759_ = lean_ctor_get(v_a_753_, 1);
lean_inc(v_snd_759_);
lean_dec(v_a_753_);
v_snd_760_ = lean_ctor_get(v_fst_757_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_fst_757_);
if (v_isSharedCheck_770_ == 0)
{
lean_object* v_unused_771_; 
v_unused_771_ = lean_ctor_get(v_fst_757_, 0);
lean_dec(v_unused_771_);
v___x_762_ = v_fst_757_;
v_isShared_763_ = v_isSharedCheck_770_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_snd_760_);
lean_dec(v_fst_757_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_770_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v_snd_759_);
lean_ctor_set(v___x_762_, 0, v_snd_760_);
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_snd_760_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_snd_759_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_765_);
v___x_767_ = v___x_755_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v_snd_772_; lean_object* v_val_773_; 
lean_inc_ref(v_fst_758_);
lean_dec(v_fst_757_);
lean_del_object(v___x_755_);
v_snd_772_ = lean_ctor_get(v_a_753_, 1);
lean_inc(v_snd_772_);
lean_dec(v_a_753_);
v_val_773_ = lean_ctor_get(v_fst_758_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v_fst_758_, 1);
v_b_731_ = v_val_773_;
v___y_732_ = v_snd_772_;
goto v___jp_730_;
}
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_a_775_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_752_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_752_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_a_786_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_737_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_737_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
v___jp_730_:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_b_731_);
lean_ctor_set(v___x_733_, 1, v___y_732_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_716_ = stack[0].m_obj;
lean_object* v_init_717_ = stack[1].m_obj;
lean_object* v___y_718_ = stack[2].m_obj;
lean_object* v___y_719_ = stack[3].m_obj;
lean_object* v___y_720_ = stack[4].m_obj;
lean_object* v___y_721_ = stack[5].m_obj;
lean_object* v___y_722_ = stack[6].m_obj;
lean_object* v___y_723_ = stack[7].m_obj;
lean_object* v___y_724_ = stack[8].m_obj;
lean_object* v___y_725_ = stack[9].m_obj;
lean_object* v___y_726_ = stack[10].m_obj;
lean_object* v___y_727_ = stack[11].m_obj;
lean_object* v___y_728_ = stack[12].m_obj;
lean_object* v_res_794_;
v_res_794_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v_t_716_, v_init_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0___boxed(lean_object* v_t_795_, lean_object* v_init_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v_t_795_, v_init_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v_t_795_);
return v_res_809_;
}
}
uint8_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(lean_object* v_xs_810_, lean_object* v_i_811_){
_start:
{
lean_object* v_size_812_; uint8_t v___x_813_; 
v_size_812_ = lean_ctor_get(v_xs_810_, 2);
v___x_813_ = lean_nat_dec_lt(v_i_811_, v_size_812_);
return v___x_813_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_810_ = stack[0].m_obj;
lean_object* v_i_811_ = stack[1].m_obj;
uint8_t v_res_814_;
v_res_814_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_xs_810_, v_i_811_);
stack->m_num = v_res_814_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0___boxed(lean_object* v_xs_815_, lean_object* v_i_816_){
_start:
{
uint8_t v_res_817_; lean_object* v_r_818_; 
v_res_817_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_xs_815_, v_i_816_);
lean_dec(v_i_816_);
lean_dec_ref(v_xs_815_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_819_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(lean_object* v_a_820_, lean_object* v_range_821_, lean_object* v_b_822_, lean_object* v_i_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_stop_836_; lean_object* v_step_837_; uint8_t v___x_838_; 
v_stop_836_ = lean_ctor_get(v_range_821_, 1);
v_step_837_ = lean_ctor_get(v_range_821_, 2);
v___x_838_ = lean_nat_dec_lt(v_i_823_, v_stop_836_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec(v_i_823_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v_b_822_);
lean_ctor_set(v___x_839_, 1, v___y_824_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; lean_object* v_snd_843_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___x_855_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_841_ = lean_box(0);
v___x_855_ = lean_box(0);
v___x_867_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0);
v___x_868_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_i_823_, v___y_825_, v___y_833_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; uint8_t v___x_870_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
v___x_870_ = lean_unbox(v_a_869_);
lean_dec(v_a_869_);
if (v___x_870_ == 0)
{
lean_object* v_lowers_871_; lean_object* v_uppers_872_; lean_object* v___y_874_; uint8_t v___x_881_; 
v_lowers_871_ = lean_ctor_get(v_a_820_, 6);
v_uppers_872_ = lean_ctor_get(v_a_820_, 7);
v___x_881_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_lowers_871_, v_i_823_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
v___x_882_ = l_outOfBounds___redArg(v___x_867_);
v___y_874_ = v___x_882_;
goto v___jp_873_;
}
else
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_PersistentArray_get_x21___redArg(v___x_867_, v_lowers_871_, v_i_823_);
v___y_874_ = v___x_883_;
goto v___jp_873_;
}
v___jp_873_:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_874_, v___x_841_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec_ref(v___y_874_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v_snd_877_; uint8_t v___x_878_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
v_snd_877_ = lean_ctor_get(v_a_876_, 1);
lean_inc(v_snd_877_);
lean_dec(v_a_876_);
v___x_878_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_uppers_872_, v_i_823_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; 
v___x_879_ = l_outOfBounds___redArg(v___x_867_);
v___y_857_ = v_snd_877_;
v___y_858_ = v___x_879_;
goto v___jp_856_;
}
else
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_PersistentArray_get_x21___redArg(v___x_867_, v_uppers_872_, v_i_823_);
v___y_857_ = v_snd_877_;
v___y_858_ = v___x_880_;
goto v___jp_856_;
}
}
else
{
lean_dec(v_i_823_);
return v___x_875_;
}
}
}
else
{
v_snd_843_ = v___y_824_;
goto v___jp_842_;
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v___y_824_);
lean_dec(v_i_823_);
v_a_884_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_868_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_868_);
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
v___jp_842_:
{
lean_object* v___x_844_; 
v___x_844_ = lean_nat_add(v_i_823_, v_step_837_);
lean_dec(v_i_823_);
v_b_822_ = v___x_841_;
v_i_823_ = v___x_844_;
v___y_824_ = v_snd_843_;
goto _start;
}
v___jp_846_:
{
if (lean_obj_tag(v___y_848_) == 1)
{
lean_object* v_val_849_; lean_object* v_d_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v_a_853_; lean_object* v_snd_854_; 
v_val_849_ = lean_ctor_get(v___y_848_, 0);
lean_inc(v_val_849_);
lean_dec_ref_known(v___y_848_, 1);
v_d_850_ = lean_ctor_get(v_val_849_, 0);
lean_inc(v_d_850_);
lean_dec(v_val_849_);
v___x_851_ = lean_nat_abs(v_d_850_);
lean_dec(v_d_850_);
v___x_852_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v___x_851_, v_i_823_, v___y_847_);
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref(v___x_852_);
v_snd_854_ = lean_ctor_get(v_a_853_, 1);
lean_inc(v_snd_854_);
lean_dec(v_a_853_);
v_snd_843_ = v_snd_854_;
goto v___jp_842_;
}
else
{
lean_dec(v___y_848_);
v_snd_843_ = v___y_847_;
goto v___jp_842_;
}
}
v___jp_856_:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_858_, v___x_841_, v___y_857_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec_ref(v___y_858_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v_dvds_861_; lean_object* v_snd_862_; lean_object* v_size_863_; uint8_t v___x_864_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v_dvds_861_ = lean_ctor_get(v_a_820_, 5);
v_snd_862_ = lean_ctor_get(v_a_860_, 1);
lean_inc(v_snd_862_);
lean_dec(v_a_860_);
v_size_863_ = lean_ctor_get(v_dvds_861_, 2);
v___x_864_ = lean_nat_dec_lt(v_i_823_, v_size_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
v___x_865_ = l_outOfBounds___redArg(v___x_855_);
v___y_847_ = v_snd_862_;
v___y_848_ = v___x_865_;
goto v___jp_846_;
}
else
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_PersistentArray_get_x21___redArg(v___x_855_, v_dvds_861_, v_i_823_);
v___y_847_ = v_snd_862_;
v___y_848_ = v___x_866_;
goto v___jp_846_;
}
}
else
{
lean_dec(v_i_823_);
return v___x_859_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_820_ = stack[0].m_obj;
lean_object* v_range_821_ = stack[1].m_obj;
lean_object* v_b_822_ = stack[2].m_obj;
lean_object* v_i_823_ = stack[3].m_obj;
lean_object* v___y_824_ = stack[4].m_obj;
lean_object* v___y_825_ = stack[5].m_obj;
lean_object* v___y_826_ = stack[6].m_obj;
lean_object* v___y_827_ = stack[7].m_obj;
lean_object* v___y_828_ = stack[8].m_obj;
lean_object* v___y_829_ = stack[9].m_obj;
lean_object* v___y_830_ = stack[10].m_obj;
lean_object* v___y_831_ = stack[11].m_obj;
lean_object* v___y_832_ = stack[12].m_obj;
lean_object* v___y_833_ = stack[13].m_obj;
lean_object* v___y_834_ = stack[14].m_obj;
lean_object* v_res_892_;
v_res_892_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_820_, v_range_821_, v_b_822_, v_i_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
stack->m_obj
 = v_res_892_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___boxed(lean_object* v_a_893_, lean_object* v_range_894_, lean_object* v_b_895_, lean_object* v_i_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_893_, v_range_894_, v_b_895_, v_i_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v_range_894_);
lean_dec_ref(v_a_893_);
return v_res_909_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_911_, v_a_919_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v_vars_924_; lean_object* v_size_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
v_vars_924_ = lean_ctor_get(v_a_923_, 0);
v_size_925_ = lean_ctor_get(v_vars_924_, 2);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_unsigned_to_nat(1u);
lean_inc(v_size_925_);
v___x_928_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v_size_925_);
lean_ctor_set(v___x_928_, 2, v___x_927_);
v___x_929_ = lean_box(0);
v___x_930_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_923_, v___x_928_, v___x_929_, v___x_926_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
lean_dec_ref_known(v___x_928_, 3);
lean_dec(v_a_923_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_947_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_947_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_947_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_947_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_snd_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_945_; 
v_snd_935_ = lean_ctor_get(v_a_931_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v_a_931_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v_a_931_, 0);
lean_dec(v_unused_946_);
v___x_937_ = v_a_931_;
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_snd_935_);
lean_dec(v_a_931_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_945_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_929_);
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_snd_935_);
v___x_940_ = v_reuseFailAlloc_944_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_940_);
v___x_942_ = v___x_933_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
else
{
return v___x_930_;
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v_a_910_);
v_a_948_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_922_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_922_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_910_ = stack[0].m_obj;
lean_object* v_a_911_ = stack[1].m_obj;
lean_object* v_a_912_ = stack[2].m_obj;
lean_object* v_a_913_ = stack[3].m_obj;
lean_object* v_a_914_ = stack[4].m_obj;
lean_object* v_a_915_ = stack[5].m_obj;
lean_object* v_a_916_ = stack[6].m_obj;
lean_object* v_a_917_ = stack[7].m_obj;
lean_object* v_a_918_ = stack[8].m_obj;
lean_object* v_a_919_ = stack[9].m_obj;
lean_object* v_a_920_ = stack[10].m_obj;
lean_object* v_res_956_;
v_res_956_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
stack->m_obj
 = v_res_956_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go___boxed(lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec(v_a_958_);
return v_res_969_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(lean_object* v_a_970_, lean_object* v_range_971_, lean_object* v_b_972_, lean_object* v_i_973_, lean_object* v_hs_974_, lean_object* v_hl_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_970_, v_range_971_, v_b_972_, v_i_973_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
return v___x_988_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_970_ = stack[0].m_obj;
lean_object* v_range_971_ = stack[1].m_obj;
lean_object* v_b_972_ = stack[2].m_obj;
lean_object* v_i_973_ = stack[3].m_obj;
lean_object* v___y_976_ = stack[6].m_obj;
lean_object* v___y_977_ = stack[7].m_obj;
lean_object* v___y_978_ = stack[8].m_obj;
lean_object* v___y_979_ = stack[9].m_obj;
lean_object* v___y_980_ = stack[10].m_obj;
lean_object* v___y_981_ = stack[11].m_obj;
lean_object* v___y_982_ = stack[12].m_obj;
lean_object* v___y_983_ = stack[13].m_obj;
lean_object* v___y_984_ = stack[14].m_obj;
lean_object* v___y_985_ = stack[15].m_obj;
lean_object* v___y_986_ = stack[16].m_obj;
lean_object* v_res_989_;
v_res_989_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(v_a_970_, v_range_971_, v_b_972_, v_i_973_, lean_box(0), lean_box(0), v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
stack->m_obj
 = v_res_989_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___boxed(lean_object** _args){
lean_object* v_a_990_ = _args[0];
lean_object* v_range_991_ = _args[1];
lean_object* v_b_992_ = _args[2];
lean_object* v_i_993_ = _args[3];
lean_object* v_hs_994_ = _args[4];
lean_object* v_hl_995_ = _args[5];
lean_object* v___y_996_ = _args[6];
lean_object* v___y_997_ = _args[7];
lean_object* v___y_998_ = _args[8];
lean_object* v___y_999_ = _args[9];
lean_object* v___y_1000_ = _args[10];
lean_object* v___y_1001_ = _args[11];
lean_object* v___y_1002_ = _args[12];
lean_object* v___y_1003_ = _args[13];
lean_object* v___y_1004_ = _args[14];
lean_object* v___y_1005_ = _args[15];
lean_object* v___y_1006_ = _args[16];
lean_object* v___y_1007_ = _args[17];
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(v_a_990_, v_range_991_, v_b_992_, v_i_993_, v_hs_994_, v_hl_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v_range_991_);
lean_dec_ref(v_a_990_);
return v_res_1008_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(lean_object* v_as_1009_, size_t v_sz_1010_, size_t v_i_1011_, lean_object* v_b_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_1009_, v_sz_1010_, v_i_1011_, v_b_1012_, v___y_1013_);
return v___x_1025_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1009_ = stack[0].m_obj;
size_t v_sz_1010_ = stack[1].m_num;
size_t v_i_1011_ = stack[2].m_num;
lean_object* v_b_1012_ = stack[3].m_obj;
lean_object* v___y_1013_ = stack[4].m_obj;
lean_object* v___y_1014_ = stack[5].m_obj;
lean_object* v___y_1015_ = stack[6].m_obj;
lean_object* v___y_1016_ = stack[7].m_obj;
lean_object* v___y_1017_ = stack[8].m_obj;
lean_object* v___y_1018_ = stack[9].m_obj;
lean_object* v___y_1019_ = stack[10].m_obj;
lean_object* v___y_1020_ = stack[11].m_obj;
lean_object* v___y_1021_ = stack[12].m_obj;
lean_object* v___y_1022_ = stack[13].m_obj;
lean_object* v___y_1023_ = stack[14].m_obj;
lean_object* v_res_1026_;
v_res_1026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(v_as_1009_, v_sz_1010_, v_i_1011_, v_b_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
stack->m_obj
 = v_res_1026_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1027_, lean_object* v_sz_1028_, lean_object* v_i_1029_, lean_object* v_b_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
size_t v_sz_boxed_1043_; size_t v_i_boxed_1044_; lean_object* v_res_1045_; 
v_sz_boxed_1043_ = lean_unbox_usize(v_sz_1028_);
lean_dec(v_sz_1028_);
v_i_boxed_1044_ = lean_unbox_usize(v_i_1029_);
lean_dec(v_i_1029_);
v_res_1045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(v_as_1027_, v_sz_boxed_1043_, v_i_boxed_1044_, v_b_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v_as_1027_);
return v_res_1045_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(lean_object* v_as_1046_, size_t v_sz_1047_, size_t v_i_1048_, lean_object* v_b_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1046_, v_sz_1047_, v_i_1048_, v_b_1049_, v___y_1050_);
return v___x_1062_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1046_ = stack[0].m_obj;
size_t v_sz_1047_ = stack[1].m_num;
size_t v_i_1048_ = stack[2].m_num;
lean_object* v_b_1049_ = stack[3].m_obj;
lean_object* v___y_1050_ = stack[4].m_obj;
lean_object* v___y_1051_ = stack[5].m_obj;
lean_object* v___y_1052_ = stack[6].m_obj;
lean_object* v___y_1053_ = stack[7].m_obj;
lean_object* v___y_1054_ = stack[8].m_obj;
lean_object* v___y_1055_ = stack[9].m_obj;
lean_object* v___y_1056_ = stack[10].m_obj;
lean_object* v___y_1057_ = stack[11].m_obj;
lean_object* v___y_1058_ = stack[12].m_obj;
lean_object* v___y_1059_ = stack[13].m_obj;
lean_object* v___y_1060_ = stack[14].m_obj;
lean_object* v_res_1063_;
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(v_as_1046_, v_sz_1047_, v_i_1048_, v_b_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
stack->m_obj
 = v_res_1063_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_as_1064_, lean_object* v_sz_1065_, lean_object* v_i_1066_, lean_object* v_b_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
size_t v_sz_boxed_1080_; size_t v_i_boxed_1081_; lean_object* v_res_1082_; 
v_sz_boxed_1080_ = lean_unbox_usize(v_sz_1065_);
lean_dec(v_sz_1065_);
v_i_boxed_1081_ = lean_unbox_usize(v_i_1066_);
lean_dec(v_i_1066_);
v_res_1082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(v_as_1064_, v_sz_boxed_1080_, v_i_boxed_1081_, v_b_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v_as_1064_);
return v_res_1082_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1083_, v_a_1091_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v_vars_1096_; lean_object* v_size_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v_vars_1096_ = lean_ctor_get(v_a_1095_, 0);
lean_inc_ref(v_vars_1096_);
lean_dec(v_a_1095_);
v_size_1097_ = lean_ctor_get(v_vars_1096_, 2);
lean_inc(v_size_1097_);
lean_dec_ref(v_vars_1096_);
v___x_1098_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0));
v___x_1099_ = lean_mk_array(v_size_1097_, v___x_1098_);
v___x_1100_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v___x_1099_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1109_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1103_ = v___x_1100_;
v_isShared_1104_ = v_isSharedCheck_1109_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1109_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v_snd_1105_; lean_object* v___x_1107_; 
v_snd_1105_ = lean_ctor_get(v_a_1101_, 1);
lean_inc(v_snd_1105_);
lean_dec(v_a_1101_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v_snd_1105_);
v___x_1107_ = v___x_1103_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_snd_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_a_1110_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1100_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1100_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1094_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1094_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1083_ = stack[0].m_obj;
lean_object* v_a_1084_ = stack[1].m_obj;
lean_object* v_a_1085_ = stack[2].m_obj;
lean_object* v_a_1086_ = stack[3].m_obj;
lean_object* v_a_1087_ = stack[4].m_obj;
lean_object* v_a_1088_ = stack[5].m_obj;
lean_object* v_a_1089_ = stack[6].m_obj;
lean_object* v_a_1090_ = stack[7].m_obj;
lean_object* v_a_1091_ = stack[8].m_obj;
lean_object* v_a_1092_ = stack[9].m_obj;
lean_object* v_res_1126_;
v_res_1126_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
stack->m_obj
 = v_res_1126_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo___boxed(lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec(v_a_1127_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(lean_object* v_info_1139_){
_start:
{
lean_object* v_maxLowerCoeff_1140_; lean_object* v_maxUpperCoeff_1141_; lean_object* v_maxDvdCoeff_1142_; lean_object* v___y_1144_; uint8_t v___x_1146_; 
v_maxLowerCoeff_1140_ = lean_ctor_get(v_info_1139_, 0);
v_maxUpperCoeff_1141_ = lean_ctor_get(v_info_1139_, 1);
v_maxDvdCoeff_1142_ = lean_ctor_get(v_info_1139_, 2);
v___x_1146_ = lean_nat_dec_le(v_maxLowerCoeff_1140_, v_maxUpperCoeff_1141_);
if (v___x_1146_ == 0)
{
v___y_1144_ = v_maxUpperCoeff_1141_;
goto v___jp_1143_;
}
else
{
v___y_1144_ = v_maxLowerCoeff_1140_;
goto v___jp_1143_;
}
v___jp_1143_:
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_nat_dec_le(v_maxDvdCoeff_1142_, v___y_1144_);
if (v___x_1145_ == 0)
{
lean_inc(v_maxDvdCoeff_1142_);
return v_maxDvdCoeff_1142_;
}
else
{
lean_inc(v___y_1144_);
return v___y_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081___boxed(lean_object* v_info_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v_info_1147_);
lean_dec_ref(v_info_1147_);
return v_res_1148_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(lean_object* v_infos_1149_, lean_object* v_x_1150_, lean_object* v_y_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1152_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1153_ = lean_array_get_borrowed(v___x_1152_, v_infos_1149_, v_x_1150_);
v___x_1154_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1153_);
v___x_1155_ = lean_array_get_borrowed(v___x_1152_, v_infos_1149_, v_y_1151_);
v___x_1156_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1155_);
v___x_1157_ = lean_nat_dec_lt(v___x_1154_, v___x_1156_);
if (v___x_1157_ == 0)
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_nat_dec_eq(v___x_1154_, v___x_1156_);
lean_dec(v___x_1156_);
lean_dec(v___x_1154_);
if (v___x_1158_ == 0)
{
uint8_t v___x_1159_; 
v___x_1159_ = 0;
return v___x_1159_;
}
else
{
uint8_t v___x_1160_; 
v___x_1160_ = 1;
return v___x_1160_;
}
}
else
{
uint8_t v___x_1161_; 
lean_dec(v___x_1156_);
lean_dec(v___x_1154_);
v___x_1161_ = 2;
return v___x_1161_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_1149_ = stack[0].m_obj;
lean_object* v_x_1150_ = stack[1].m_obj;
lean_object* v_y_1151_ = stack[2].m_obj;
uint8_t v_res_1162_;
v_res_1162_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1149_, v_x_1150_, v_y_1151_);
stack->m_num = v_res_1162_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081___boxed(lean_object* v_infos_1163_, lean_object* v_x_1164_, lean_object* v_y_1165_){
_start:
{
uint8_t v_res_1166_; lean_object* v_r_1167_; 
v_res_1166_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1163_, v_x_1164_, v_y_1165_);
lean_dec(v_y_1165_);
lean_dec(v_x_1164_);
lean_dec_ref(v_infos_1163_);
v_r_1167_ = lean_box(v_res_1166_);
return v_r_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(lean_object* v_info_1168_){
_start:
{
lean_object* v_maxLowerCoeff_1169_; lean_object* v_maxUpperCoeff_1170_; lean_object* v_maxDvdCoeff_1171_; lean_object* v___y_1173_; uint8_t v___x_1175_; 
v_maxLowerCoeff_1169_ = lean_ctor_get(v_info_1168_, 0);
v_maxUpperCoeff_1170_ = lean_ctor_get(v_info_1168_, 1);
v_maxDvdCoeff_1171_ = lean_ctor_get(v_info_1168_, 2);
v___x_1175_ = lean_nat_dec_le(v_maxLowerCoeff_1169_, v_maxUpperCoeff_1170_);
if (v___x_1175_ == 0)
{
v___y_1173_ = v_maxLowerCoeff_1169_;
goto v___jp_1172_;
}
else
{
v___y_1173_ = v_maxUpperCoeff_1170_;
goto v___jp_1172_;
}
v___jp_1172_:
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_nat_dec_le(v_maxDvdCoeff_1171_, v___y_1173_);
if (v___x_1174_ == 0)
{
lean_inc(v_maxDvdCoeff_1171_);
return v_maxDvdCoeff_1171_;
}
else
{
lean_inc(v___y_1173_);
return v___y_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082___boxed(lean_object* v_info_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v_info_1176_);
lean_dec_ref(v_info_1176_);
return v_res_1177_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(lean_object* v_infos_1178_, lean_object* v_x_1179_, lean_object* v_y_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1181_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1182_ = lean_array_get_borrowed(v___x_1181_, v_infos_1178_, v_x_1179_);
v___x_1183_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1182_);
v___x_1184_ = lean_array_get_borrowed(v___x_1181_, v_infos_1178_, v_y_1180_);
v___x_1185_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1184_);
v___x_1186_ = lean_nat_dec_lt(v___x_1183_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint8_t v___x_1187_; 
v___x_1187_ = lean_nat_dec_eq(v___x_1183_, v___x_1185_);
lean_dec(v___x_1185_);
lean_dec(v___x_1183_);
if (v___x_1187_ == 0)
{
uint8_t v___x_1188_; 
v___x_1188_ = 0;
return v___x_1188_;
}
else
{
uint8_t v___x_1189_; 
v___x_1189_ = 1;
return v___x_1189_;
}
}
else
{
uint8_t v___x_1190_; 
lean_dec(v___x_1185_);
lean_dec(v___x_1183_);
v___x_1190_ = 2;
return v___x_1190_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_1178_ = stack[0].m_obj;
lean_object* v_x_1179_ = stack[1].m_obj;
lean_object* v_y_1180_ = stack[2].m_obj;
uint8_t v_res_1191_;
v_res_1191_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1178_, v_x_1179_, v_y_1180_);
stack->m_num = v_res_1191_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082___boxed(lean_object* v_infos_1192_, lean_object* v_x_1193_, lean_object* v_y_1194_){
_start:
{
uint8_t v_res_1195_; lean_object* v_r_1196_; 
v_res_1195_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1192_, v_x_1193_, v_y_1194_);
lean_dec(v_y_1194_);
lean_dec(v_x_1193_);
lean_dec_ref(v_infos_1192_);
v_r_1196_ = lean_box(v_res_1195_);
return v_r_1196_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(lean_object* v_infos_1197_, lean_object* v_x_1198_, lean_object* v_y_1199_){
_start:
{
uint8_t v___y_1201_; uint8_t v___x_1206_; 
v___x_1206_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1197_, v_x_1198_, v_y_1199_);
if (v___x_1206_ == 1)
{
uint8_t v___x_1207_; 
v___x_1207_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1197_, v_x_1198_, v_y_1199_);
v___y_1201_ = v___x_1207_;
goto v___jp_1200_;
}
else
{
v___y_1201_ = v___x_1206_;
goto v___jp_1200_;
}
v___jp_1200_:
{
if (v___y_1201_ == 1)
{
uint8_t v___x_1202_; 
v___x_1202_ = lean_nat_dec_lt(v_x_1198_, v_y_1199_);
if (v___x_1202_ == 0)
{
uint8_t v___x_1203_; 
v___x_1203_ = lean_nat_dec_eq(v_x_1198_, v_y_1199_);
if (v___x_1203_ == 0)
{
uint8_t v___x_1204_; 
v___x_1204_ = 2;
return v___x_1204_;
}
else
{
return v___y_1201_;
}
}
else
{
uint8_t v___x_1205_; 
v___x_1205_ = 0;
return v___x_1205_;
}
}
else
{
return v___y_1201_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_1197_ = stack[0].m_obj;
lean_object* v_x_1198_ = stack[1].m_obj;
lean_object* v_y_1199_ = stack[2].m_obj;
uint8_t v_res_1208_;
v_res_1208_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1197_, v_x_1198_, v_y_1199_);
stack->m_num = v_res_1208_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp___boxed(lean_object* v_infos_1209_, lean_object* v_x_1210_, lean_object* v_y_1211_){
_start:
{
uint8_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1209_, v_x_1210_, v_y_1211_);
lean_dec(v_y_1211_);
lean_dec(v_x_1210_);
lean_dec_ref(v_infos_1209_);
v_r_1213_ = lean_box(v_res_1212_);
return v_r_1213_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(lean_object* v_infos_1214_, lean_object* v_x_1215_, lean_object* v_y_1216_){
_start:
{
uint8_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1217_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1214_, v_x_1215_, v_y_1216_);
v___x_1218_ = lean_box(v___x_1217_);
v___x_1219_ = lean_obj_tag_nat(v___x_1218_);
lean_dec(v___x_1218_);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = lean_nat_dec_eq(v___x_1219_, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_1214_ = stack[0].m_obj;
lean_object* v_x_1215_ = stack[1].m_obj;
lean_object* v_y_1216_ = stack[2].m_obj;
uint8_t v_res_1222_;
v_res_1222_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1214_, v_x_1215_, v_y_1216_);
stack->m_num = v_res_1222_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0___boxed(lean_object* v_infos_1223_, lean_object* v_x_1224_, lean_object* v_y_1225_){
_start:
{
uint8_t v_res_1226_; lean_object* v_r_1227_; 
v_res_1226_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1223_, v_x_1224_, v_y_1225_);
lean_dec(v_y_1225_);
lean_dec(v_x_1224_);
lean_dec_ref(v_infos_1223_);
v_r_1227_ = lean_box(v_res_1226_);
return v_r_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(lean_object* v_infos_1228_, lean_object* v_hi_1229_, lean_object* v_pivot_1230_, lean_object* v_as_1231_, lean_object* v_i_1232_, lean_object* v_k_1233_){
_start:
{
uint8_t v___x_1234_; 
v___x_1234_ = lean_nat_dec_lt(v_k_1233_, v_hi_1229_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec(v_k_1233_);
v___x_1235_ = lean_array_fswap(v_as_1231_, v_i_1232_, v_hi_1229_);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_i_1232_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1237_ = lean_array_fget_borrowed(v_as_1231_, v_k_1233_);
v___x_1238_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1228_, v___x_1237_, v_pivot_1230_);
v___x_1239_ = lean_box(v___x_1238_);
v___x_1240_ = lean_obj_tag_nat(v___x_1239_);
lean_dec(v___x_1239_);
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = lean_nat_dec_eq(v___x_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_nat_add(v_k_1233_, v___x_1243_);
lean_dec(v_k_1233_);
v_k_1233_ = v___x_1244_;
goto _start;
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1246_ = lean_array_fswap(v_as_1231_, v_i_1232_, v_k_1233_);
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_nat_add(v_i_1232_, v___x_1247_);
lean_dec(v_i_1232_);
v___x_1249_ = lean_nat_add(v_k_1233_, v___x_1247_);
lean_dec(v_k_1233_);
v_as_1231_ = v___x_1246_;
v_i_1232_ = v___x_1248_;
v_k_1233_ = v___x_1249_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg___boxed(lean_object* v_infos_1251_, lean_object* v_hi_1252_, lean_object* v_pivot_1253_, lean_object* v_as_1254_, lean_object* v_i_1255_, lean_object* v_k_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_infos_1251_, v_hi_1252_, v_pivot_1253_, v_as_1254_, v_i_1255_, v_k_1256_);
lean_dec(v_pivot_1253_);
lean_dec(v_hi_1252_);
lean_dec_ref(v_infos_1251_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(lean_object* v_infos_1258_, lean_object* v_n_1259_, lean_object* v_as_1260_, lean_object* v_lo_1261_, lean_object* v_hi_1262_){
_start:
{
lean_object* v___y_1264_; uint8_t v___x_1274_; 
v___x_1274_ = lean_nat_dec_lt(v_lo_1261_, v_hi_1262_);
if (v___x_1274_ == 0)
{
lean_dec(v_lo_1261_);
return v_as_1260_;
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v_mid_1277_; lean_object* v___y_1279_; lean_object* v___y_1285_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1275_ = lean_nat_add(v_lo_1261_, v_hi_1262_);
v___x_1276_ = lean_unsigned_to_nat(1u);
v_mid_1277_ = lean_nat_shiftr(v___x_1275_, v___x_1276_);
lean_dec(v___x_1275_);
v___x_1290_ = lean_array_fget_borrowed(v_as_1260_, v_mid_1277_);
v___x_1291_ = lean_array_fget_borrowed(v_as_1260_, v_lo_1261_);
v___x_1292_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1258_, v___x_1290_, v___x_1291_);
if (v___x_1292_ == 0)
{
v___y_1285_ = v_as_1260_;
goto v___jp_1284_;
}
else
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_array_fswap(v_as_1260_, v_lo_1261_, v_mid_1277_);
v___y_1285_ = v___x_1293_;
goto v___jp_1284_;
}
v___jp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1280_ = lean_array_fget_borrowed(v___y_1279_, v_mid_1277_);
v___x_1281_ = lean_array_fget_borrowed(v___y_1279_, v_hi_1262_);
v___x_1282_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1258_, v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_dec(v_mid_1277_);
v___y_1264_ = v___y_1279_;
goto v___jp_1263_;
}
else
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_array_fswap(v___y_1279_, v_mid_1277_, v_hi_1262_);
lean_dec(v_mid_1277_);
v___y_1264_ = v___x_1283_;
goto v___jp_1263_;
}
}
v___jp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1286_ = lean_array_fget_borrowed(v___y_1285_, v_hi_1262_);
v___x_1287_ = lean_array_fget_borrowed(v___y_1285_, v_lo_1261_);
v___x_1288_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_infos_1258_, v___x_1286_, v___x_1287_);
if (v___x_1288_ == 0)
{
v___y_1279_ = v___y_1285_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_array_fswap(v___y_1285_, v_lo_1261_, v_hi_1262_);
v___y_1279_ = v___x_1289_;
goto v___jp_1278_;
}
}
}
v___jp_1263_:
{
lean_object* v_pivot_1265_; lean_object* v___x_1266_; lean_object* v_fst_1267_; lean_object* v_snd_1268_; uint8_t v___x_1269_; 
v_pivot_1265_ = lean_array_fget(v___y_1264_, v_hi_1262_);
lean_inc_n(v_lo_1261_, 2);
v___x_1266_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_infos_1258_, v_hi_1262_, v_pivot_1265_, v___y_1264_, v_lo_1261_, v_lo_1261_);
lean_dec(v_pivot_1265_);
v_fst_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_fst_1267_);
v_snd_1268_ = lean_ctor_get(v___x_1266_, 1);
lean_inc(v_snd_1268_);
lean_dec_ref(v___x_1266_);
v___x_1269_ = lean_nat_dec_le(v_hi_1262_, v_fst_1267_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1258_, v_n_1259_, v_snd_1268_, v_lo_1261_, v_fst_1267_);
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_add(v_fst_1267_, v___x_1271_);
lean_dec(v_fst_1267_);
v_as_1260_ = v___x_1270_;
v_lo_1261_ = v___x_1272_;
goto _start;
}
else
{
lean_dec(v_fst_1267_);
lean_dec(v_lo_1261_);
return v_snd_1268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___boxed(lean_object* v_infos_1294_, lean_object* v_n_1295_, lean_object* v_as_1296_, lean_object* v_lo_1297_, lean_object* v_hi_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1294_, v_n_1295_, v_as_1296_, v_lo_1297_, v_hi_1298_);
lean_dec(v_hi_1298_);
lean_dec(v_n_1295_);
lean_dec_ref(v_infos_1294_);
return v_res_1299_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(lean_object* v_infos_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1329_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1329_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1329_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_vars_1309_; lean_object* v_size_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_vars_1309_ = lean_ctor_get(v_a_1305_, 0);
lean_inc_ref(v_vars_1309_);
lean_dec(v_a_1305_);
v_size_1310_ = lean_ctor_get(v_vars_1309_, 2);
lean_inc(v_size_1310_);
lean_dec_ref(v_vars_1309_);
v___x_1311_ = l_Array_range(v_size_1310_);
v___x_1312_ = lean_array_get_size(v___x_1311_);
v___x_1320_ = lean_unsigned_to_nat(0u);
v___x_1321_ = lean_nat_dec_eq(v___x_1312_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___y_1325_; uint8_t v___x_1327_; 
v___x_1322_ = lean_unsigned_to_nat(1u);
v___x_1323_ = lean_nat_sub(v___x_1312_, v___x_1322_);
v___x_1327_ = lean_nat_dec_le(v___x_1320_, v___x_1323_);
if (v___x_1327_ == 0)
{
lean_inc(v___x_1323_);
v___y_1325_ = v___x_1323_;
goto v___jp_1324_;
}
else
{
v___y_1325_ = v___x_1320_;
goto v___jp_1324_;
}
v___jp_1324_:
{
uint8_t v___x_1326_; 
v___x_1326_ = lean_nat_dec_le(v___y_1325_, v___x_1323_);
if (v___x_1326_ == 0)
{
lean_dec(v___x_1323_);
lean_inc(v___y_1325_);
v___y_1314_ = v___y_1325_;
v___y_1315_ = v___y_1325_;
goto v___jp_1313_;
}
else
{
v___y_1314_ = v___y_1325_;
v___y_1315_ = v___x_1323_;
goto v___jp_1313_;
}
}
}
else
{
lean_object* v___x_1328_; 
lean_del_object(v___x_1307_);
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1311_);
return v___x_1328_;
}
v___jp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1300_, v___x_1312_, v___x_1311_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1316_);
v___x_1318_ = v___x_1307_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
v_a_1330_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1304_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1304_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_1300_ = stack[0].m_obj;
lean_object* v_a_1301_ = stack[1].m_obj;
lean_object* v_a_1302_ = stack[2].m_obj;
lean_object* v_res_1338_;
v_res_1338_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(v_infos_1300_, v_a_1301_, v_a_1302_);
stack->m_obj
 = v_res_1338_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg___boxed(lean_object* v_infos_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(v_infos_1339_, v_a_1340_, v_a_1341_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_infos_1339_);
return v_res_1343_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(lean_object* v_infos_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(v_infos_1344_, v_a_1345_, v_a_1353_);
return v___x_1356_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_1344_ = stack[0].m_obj;
lean_object* v_a_1345_ = stack[1].m_obj;
lean_object* v_a_1346_ = stack[2].m_obj;
lean_object* v_a_1347_ = stack[3].m_obj;
lean_object* v_a_1348_ = stack[4].m_obj;
lean_object* v_a_1349_ = stack[5].m_obj;
lean_object* v_a_1350_ = stack[6].m_obj;
lean_object* v_a_1351_ = stack[7].m_obj;
lean_object* v_a_1352_ = stack[8].m_obj;
lean_object* v_a_1353_ = stack[9].m_obj;
lean_object* v_a_1354_ = stack[10].m_obj;
lean_object* v_res_1357_;
v_res_1357_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_infos_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
stack->m_obj
 = v_res_1357_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___boxed(lean_object* v_infos_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_infos_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_infos_1358_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(lean_object* v_infos_1371_, lean_object* v_n_1372_, lean_object* v_as_1373_, lean_object* v_lo_1374_, lean_object* v_hi_1375_, lean_object* v_w_1376_, lean_object* v_hlo_1377_, lean_object* v_hhi_1378_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_infos_1371_, v_n_1372_, v_as_1373_, v_lo_1374_, v_hi_1375_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___boxed(lean_object* v_infos_1380_, lean_object* v_n_1381_, lean_object* v_as_1382_, lean_object* v_lo_1383_, lean_object* v_hi_1384_, lean_object* v_w_1385_, lean_object* v_hlo_1386_, lean_object* v_hhi_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(v_infos_1380_, v_n_1381_, v_as_1382_, v_lo_1383_, v_hi_1384_, v_w_1385_, v_hlo_1386_, v_hhi_1387_);
lean_dec(v_hi_1384_);
lean_dec(v_n_1381_);
lean_dec_ref(v_infos_1380_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(lean_object* v_infos_1389_, lean_object* v_n_1390_, lean_object* v_lo_1391_, lean_object* v_hi_1392_, lean_object* v_hhi_1393_, lean_object* v_pivot_1394_, lean_object* v_as_1395_, lean_object* v_i_1396_, lean_object* v_k_1397_, lean_object* v_ilo_1398_, lean_object* v_ik_1399_, lean_object* v_w_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_infos_1389_, v_hi_1392_, v_pivot_1394_, v_as_1395_, v_i_1396_, v_k_1397_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___boxed(lean_object* v_infos_1402_, lean_object* v_n_1403_, lean_object* v_lo_1404_, lean_object* v_hi_1405_, lean_object* v_hhi_1406_, lean_object* v_pivot_1407_, lean_object* v_as_1408_, lean_object* v_i_1409_, lean_object* v_k_1410_, lean_object* v_ilo_1411_, lean_object* v_ik_1412_, lean_object* v_w_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(v_infos_1402_, v_n_1403_, v_lo_1404_, v_hi_1405_, v_hhi_1406_, v_pivot_1407_, v_as_1408_, v_i_1409_, v_k_1410_, v_ilo_1411_, v_ik_1412_, v_w_1413_);
lean_dec(v_pivot_1407_);
lean_dec(v_hi_1405_);
lean_dec(v_lo_1404_);
lean_dec(v_n_1403_);
lean_dec_ref(v_infos_1402_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(lean_object* v_perm_1415_, lean_object* v_range_1416_, lean_object* v_b_1417_, lean_object* v_i_1418_){
_start:
{
lean_object* v_stop_1419_; lean_object* v_step_1420_; uint8_t v___x_1421_; 
v_stop_1419_ = lean_ctor_get(v_range_1416_, 1);
v_step_1420_ = lean_ctor_get(v_range_1416_, 2);
v___x_1421_ = lean_nat_dec_lt(v_i_1418_, v_stop_1419_);
if (v___x_1421_ == 0)
{
lean_dec(v_i_1418_);
return v_b_1417_;
}
else
{
lean_object* v___x_1422_; lean_object* v_inv_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_array_fget_borrowed(v_perm_1415_, v_i_1418_);
lean_inc(v_i_1418_);
v_inv_1423_ = lean_array_set(v_b_1417_, v___x_1422_, v_i_1418_);
v___x_1424_ = lean_nat_add(v_i_1418_, v_step_1420_);
lean_dec(v_i_1418_);
v_b_1417_ = v_inv_1423_;
v_i_1418_ = v___x_1424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg___boxed(lean_object* v_perm_1426_, lean_object* v_range_1427_, lean_object* v_b_1428_, lean_object* v_i_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1426_, v_range_1427_, v_b_1428_, v_i_1429_);
lean_dec_ref(v_range_1427_);
lean_dec_ref(v_perm_1426_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(lean_object* v_perm_1431_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v_inv_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1432_ = lean_array_get_size(v_perm_1431_);
v___x_1433_ = lean_unsigned_to_nat(0u);
v_inv_1434_ = lean_mk_array(v___x_1432_, v___x_1433_);
v___x_1435_ = lean_unsigned_to_nat(1u);
v___x_1436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1433_);
lean_ctor_set(v___x_1436_, 1, v___x_1432_);
lean_ctor_set(v___x_1436_, 2, v___x_1435_);
v___x_1437_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1431_, v___x_1436_, v_inv_1434_, v___x_1433_);
lean_dec_ref_known(v___x_1436_, 3);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv___boxed(lean_object* v_perm_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_perm_1438_);
lean_dec_ref(v_perm_1438_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(lean_object* v_perm_1440_, lean_object* v_range_1441_, lean_object* v_b_1442_, lean_object* v_i_1443_, lean_object* v_hs_1444_, lean_object* v_hl_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1440_, v_range_1441_, v_b_1442_, v_i_1443_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___boxed(lean_object* v_perm_1447_, lean_object* v_range_1448_, lean_object* v_b_1449_, lean_object* v_i_1450_, lean_object* v_hs_1451_, lean_object* v_hl_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(v_perm_1447_, v_range_1448_, v_b_1449_, v_i_1450_, v_hs_1451_, v_hl_1452_);
lean_dec_ref(v_range_1448_);
lean_dec_ref(v_perm_1447_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_reorder(lean_object* v_p_1454_, lean_object* v_old2new_1455_){
_start:
{
if (lean_obj_tag(v_p_1454_) == 0)
{
return v_p_1454_;
}
else
{
lean_object* v_k_1456_; lean_object* v_v_1457_; lean_object* v_p_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1468_; 
v_k_1456_ = lean_ctor_get(v_p_1454_, 0);
v_v_1457_ = lean_ctor_get(v_p_1454_, 1);
v_p_1458_ = lean_ctor_get(v_p_1454_, 2);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_p_1454_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1460_ = v_p_1454_;
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_p_1458_);
lean_inc(v_v_1457_);
lean_inc(v_k_1456_);
lean_dec(v_p_1454_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = lean_array_get_borrowed(v___x_1462_, v_old2new_1455_, v_v_1457_);
lean_dec(v_v_1457_);
v___x_1464_ = l_Int_Internal_Linear_Poly_reorder(v_p_1458_, v_old2new_1455_);
lean_inc(v___x_1463_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 2, v___x_1464_);
lean_ctor_set(v___x_1460_, 1, v___x_1463_);
v___x_1466_ = v___x_1460_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_k_1456_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v___x_1464_);
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
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_reorder___boxed(lean_object* v_p_1469_, lean_object* v_old2new_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Int_Internal_Linear_Poly_reorder(v_p_1469_, v_old2new_1470_);
lean_dec_ref(v_old2new_1470_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(lean_object* v_c_1472_, lean_object* v_old2new_1473_){
_start:
{
lean_object* v_d_1474_; lean_object* v_p_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v_d_1474_ = lean_ctor_get(v_c_1472_, 0);
lean_inc(v_d_1474_);
v_p_1475_ = lean_ctor_get(v_c_1472_, 1);
lean_inc_ref(v_p_1475_);
v___x_1476_ = l_Int_Internal_Linear_Poly_reorder(v_p_1475_, v_old2new_1473_);
v___x_1477_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_c_1472_);
v___x_1478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1478_, 0, v_d_1474_);
lean_ctor_set(v___x_1478_, 1, v___x_1476_);
lean_ctor_set(v___x_1478_, 2, v___x_1477_);
v___x_1479_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v___x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder___boxed(lean_object* v_c_1480_, lean_object* v_old2new_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_c_1480_, v_old2new_1481_);
lean_dec_ref(v_old2new_1481_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(lean_object* v_c_1483_, lean_object* v_old2new_1484_){
_start:
{
lean_object* v_p_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v_p_1485_ = lean_ctor_get(v_c_1483_, 0);
lean_inc_ref(v_p_1485_);
v___x_1486_ = l_Int_Internal_Linear_Poly_reorder(v_p_1485_, v_old2new_1484_);
v___x_1487_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_1487_, 0, v_c_1483_);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder___boxed(lean_object* v_c_1490_, lean_object* v_old2new_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_c_1490_, v_old2new_1491_);
lean_dec_ref(v_old2new_1491_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(lean_object* v_c_1493_, lean_object* v_old2new_1494_){
_start:
{
lean_object* v_p_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_p_1495_ = lean_ctor_get(v_c_1493_, 0);
lean_inc_ref(v_p_1495_);
v___x_1496_ = l_Int_Internal_Linear_Poly_reorder(v_p_1495_, v_old2new_1494_);
v___x_1497_ = lean_alloc_ctor(16, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_c_1493_);
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1496_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder___boxed(lean_object* v_c_1500_, lean_object* v_old2new_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_c_1500_, v_old2new_1501_);
lean_dec_ref(v_old2new_1501_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(lean_object* v_c_1503_, lean_object* v_old2new_1504_){
_start:
{
lean_object* v_p_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_p_1505_ = lean_ctor_get(v_c_1503_, 0);
lean_inc_ref(v_p_1505_);
v___x_1506_ = l_Int_Internal_Linear_Poly_reorder(v_p_1505_, v_old2new_1504_);
v___x_1507_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1507_, 0, v_c_1503_);
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder___boxed(lean_object* v_c_1510_, lean_object* v_old2new_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_c_1510_, v_old2new_1511_);
lean_dec_ref(v_old2new_1511_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(lean_object* v_new2old_1513_, lean_object* v_inst_1514_, lean_object* v_m_1515_, lean_object* v_i_1516_, lean_object* v_h_1517_, lean_object* v_____s_1518_){
_start:
{
lean_object* v_j_1519_; lean_object* v___x_1520_; lean_object* v_r_1521_; lean_object* v___x_1522_; 
v_j_1519_ = lean_array_fget_borrowed(v_new2old_1513_, v_i_1516_);
v___x_1520_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_1514_, v_m_1515_, v_j_1519_);
v_r_1521_ = l_Lean_PersistentArray_push___redArg(v_____s_1518_, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1522_, 0, v_r_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed(lean_object* v_new2old_1523_, lean_object* v_inst_1524_, lean_object* v_m_1525_, lean_object* v_i_1526_, lean_object* v_h_1527_, lean_object* v_____s_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(v_new2old_1523_, v_inst_1524_, v_m_1525_, v_i_1526_, v_h_1527_, v_____s_1528_);
lean_dec(v_i_1526_);
lean_dec_ref(v_m_1525_);
lean_dec(v_inst_1524_);
lean_dec_ref(v_new2old_1523_);
return v_res_1529_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = lean_unsigned_to_nat(32u);
v___x_1550_ = lean_mk_empty_array_with_capacity(v___x_1549_);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11(void){
_start:
{
size_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v_r_1557_; 
v___x_1552_ = ((size_t)5ULL);
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = lean_unsigned_to_nat(32u);
v___x_1555_ = lean_mk_empty_array_with_capacity(v___x_1554_);
v___x_1556_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10);
v_r_1557_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_r_1557_, 0, v___x_1556_);
lean_ctor_set(v_r_1557_, 1, v___x_1555_);
lean_ctor_set(v_r_1557_, 2, v___x_1553_);
lean_ctor_set(v_r_1557_, 3, v___x_1553_);
lean_ctor_set_usize(v_r_1557_, 4, v___x_1552_);
return v_r_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(lean_object* v_inst_1558_, lean_object* v_m_1559_, lean_object* v_new2old_1560_){
_start:
{
lean_object* v___f_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_r_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_inc_ref(v_new2old_1560_);
v___f_1561_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1561_, 0, v_new2old_1560_);
lean_closure_set(v___f_1561_, 1, v_inst_1558_);
lean_closure_set(v___f_1561_, 2, v_m_1559_);
v___x_1562_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9));
v___x_1563_ = lean_unsigned_to_nat(0u);
v_r_1564_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11);
v___x_1565_ = lean_array_get_size(v_new2old_1560_);
lean_dec_ref(v_new2old_1560_);
v___x_1566_ = lean_unsigned_to_nat(1u);
v___x_1567_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1563_);
lean_ctor_set(v___x_1567_, 1, v___x_1565_);
lean_ctor_set(v___x_1567_, 2, v___x_1566_);
v___x_1568_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), v___x_1562_, v___x_1567_, v___f_1561_, v_r_1564_, v___x_1563_, lean_box(0), lean_box(0));
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap(lean_object* v_00_u03b1_1569_, lean_object* v_inst_1570_, lean_object* v_m_1571_, lean_object* v_new2old_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v_inst_1570_, v_m_1571_, v_new2old_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_, lean_object* v_x_1577_){
_start:
{
lean_object* v_ks_1578_; lean_object* v_vs_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1603_; 
v_ks_1578_ = lean_ctor_get(v_x_1574_, 0);
v_vs_1579_ = lean_ctor_get(v_x_1574_, 1);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_x_1574_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1581_ = v_x_1574_;
v_isShared_1582_ = v_isSharedCheck_1603_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_vs_1579_);
lean_inc(v_ks_1578_);
lean_dec(v_x_1574_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1603_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = lean_array_get_size(v_ks_1578_);
v___x_1584_ = lean_nat_dec_lt(v_x_1575_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
lean_dec(v_x_1575_);
v___x_1585_ = lean_array_push(v_ks_1578_, v_x_1576_);
v___x_1586_ = lean_array_push(v_vs_1579_, v_x_1577_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 1, v___x_1586_);
lean_ctor_set(v___x_1581_, 0, v___x_1585_);
v___x_1588_ = v___x_1581_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
else
{
lean_object* v_k_x27_1590_; uint8_t v___x_1591_; 
v_k_x27_1590_ = lean_array_fget_borrowed(v_ks_1578_, v_x_1575_);
v___x_1591_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_1576_, v_k_x27_1590_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1593_; 
if (v_isShared_1582_ == 0)
{
v___x_1593_ = v___x_1581_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_ks_1578_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_vs_1579_);
v___x_1593_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_unsigned_to_nat(1u);
v___x_1595_ = lean_nat_add(v_x_1575_, v___x_1594_);
lean_dec(v_x_1575_);
v_x_1574_ = v___x_1593_;
v_x_1575_ = v___x_1595_;
goto _start;
}
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1598_ = lean_array_fset(v_ks_1578_, v_x_1575_, v_x_1576_);
v___x_1599_ = lean_array_fset(v_vs_1579_, v_x_1575_, v_x_1577_);
lean_dec(v_x_1575_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 1, v___x_1599_);
lean_ctor_set(v___x_1581_, 0, v___x_1598_);
v___x_1601_ = v___x_1581_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v___x_1599_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1604_, lean_object* v_k_1605_, lean_object* v_v_1606_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_unsigned_to_nat(0u);
v___x_1608_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1604_, v___x_1607_, v_k_1605_, v_v_1606_);
return v___x_1608_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1609_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(lean_object* v_x_1610_, size_t v_x_1611_, size_t v_x_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_){
_start:
{
if (lean_obj_tag(v_x_1610_) == 0)
{
lean_object* v_es_1615_; size_t v___x_1616_; size_t v___x_1617_; lean_object* v_j_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_es_1615_ = lean_ctor_get(v_x_1610_, 0);
v___x_1616_ = ((size_t)31ULL);
v___x_1617_ = lean_usize_land(v_x_1611_, v___x_1616_);
v_j_1618_ = lean_usize_to_nat(v___x_1617_);
v___x_1619_ = lean_array_get_size(v_es_1615_);
v___x_1620_ = lean_nat_dec_lt(v_j_1618_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_dec(v_j_1618_);
lean_dec(v_x_1614_);
lean_dec_ref(v_x_1613_);
return v_x_1610_;
}
else
{
lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1659_; 
lean_inc_ref(v_es_1615_);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_x_1610_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; 
v_unused_1660_ = lean_ctor_get(v_x_1610_, 0);
lean_dec(v_unused_1660_);
v___x_1622_ = v_x_1610_;
v_isShared_1623_ = v_isSharedCheck_1659_;
goto v_resetjp_1621_;
}
else
{
lean_dec(v_x_1610_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1659_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v_v_1624_; lean_object* v___x_1625_; lean_object* v_xs_x27_1626_; lean_object* v___y_1628_; 
v_v_1624_ = lean_array_fget(v_es_1615_, v_j_1618_);
v___x_1625_ = lean_box(0);
v_xs_x27_1626_ = lean_array_fset(v_es_1615_, v_j_1618_, v___x_1625_);
switch(lean_obj_tag(v_v_1624_))
{
case 0:
{
lean_object* v_key_1633_; lean_object* v_val_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1644_; 
v_key_1633_ = lean_ctor_get(v_v_1624_, 0);
v_val_1634_ = lean_ctor_get(v_v_1624_, 1);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_v_1624_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1636_ = v_v_1624_;
v_isShared_1637_ = v_isSharedCheck_1644_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_val_1634_);
lean_inc(v_key_1633_);
lean_dec(v_v_1624_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1644_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
uint8_t v___x_1638_; 
v___x_1638_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_1613_, v_key_1633_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_del_object(v___x_1636_);
v___x_1639_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1633_, v_val_1634_, v_x_1613_, v_x_1614_);
v___x_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
v___y_1628_ = v___x_1640_;
goto v___jp_1627_;
}
else
{
lean_object* v___x_1642_; 
lean_dec(v_val_1634_);
lean_dec(v_key_1633_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 1, v_x_1614_);
lean_ctor_set(v___x_1636_, 0, v_x_1613_);
v___x_1642_ = v___x_1636_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_x_1613_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_x_1614_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
v___y_1628_ = v___x_1642_;
goto v___jp_1627_;
}
}
}
}
case 1:
{
lean_object* v_node_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1657_; 
v_node_1645_ = lean_ctor_get(v_v_1624_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_v_1624_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1647_ = v_v_1624_;
v_isShared_1648_ = v_isSharedCheck_1657_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_node_1645_);
lean_dec(v_v_1624_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1657_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
size_t v___x_1649_; size_t v___x_1650_; size_t v___x_1651_; size_t v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; 
v___x_1649_ = ((size_t)5ULL);
v___x_1650_ = lean_usize_shift_right(v_x_1611_, v___x_1649_);
v___x_1651_ = ((size_t)1ULL);
v___x_1652_ = lean_usize_add(v_x_1612_, v___x_1651_);
v___x_1653_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_node_1645_, v___x_1650_, v___x_1652_, v_x_1613_, v_x_1614_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1653_);
v___x_1655_ = v___x_1647_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
v___y_1628_ = v___x_1655_;
goto v___jp_1627_;
}
}
}
default: 
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v_x_1613_);
lean_ctor_set(v___x_1658_, 1, v_x_1614_);
v___y_1628_ = v___x_1658_;
goto v___jp_1627_;
}
}
v___jp_1627_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = lean_array_fset(v_xs_x27_1626_, v_j_1618_, v___y_1628_);
lean_dec(v_j_1618_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1629_);
v___x_1631_ = v___x_1622_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
else
{
lean_object* v_ks_1661_; lean_object* v_vs_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1680_; 
v_ks_1661_ = lean_ctor_get(v_x_1610_, 0);
v_vs_1662_ = lean_ctor_get(v_x_1610_, 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_x_1610_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1664_ = v_x_1610_;
v_isShared_1665_ = v_isSharedCheck_1680_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_vs_1662_);
lean_inc(v_ks_1661_);
lean_dec(v_x_1610_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1680_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_ks_1661_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_vs_1662_);
v___x_1667_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v_newNode_1668_; size_t v___x_1669_; uint8_t v___x_1670_; 
v_newNode_1668_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v___x_1667_, v_x_1613_, v_x_1614_);
v___x_1669_ = ((size_t)7ULL);
v___x_1670_ = lean_usize_dec_le(v___x_1669_, v_x_1612_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1671_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1668_);
v___x_1672_ = lean_unsigned_to_nat(4u);
v___x_1673_ = lean_nat_dec_lt(v___x_1671_, v___x_1672_);
lean_dec(v___x_1671_);
if (v___x_1673_ == 0)
{
lean_object* v_ks_1674_; lean_object* v_vs_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v_ks_1674_ = lean_ctor_get(v_newNode_1668_, 0);
lean_inc_ref(v_ks_1674_);
v_vs_1675_ = lean_ctor_get(v_newNode_1668_, 1);
lean_inc_ref(v_vs_1675_);
lean_dec_ref(v_newNode_1668_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0);
v___x_1678_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_x_1612_, v_ks_1674_, v_vs_1675_, v___x_1676_, v___x_1677_);
lean_dec_ref(v_vs_1675_);
lean_dec_ref(v_ks_1674_);
return v___x_1678_;
}
else
{
return v_newNode_1668_;
}
}
else
{
return v_newNode_1668_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1610_ = stack[0].m_obj;
size_t v_x_1611_ = stack[1].m_num;
size_t v_x_1612_ = stack[2].m_num;
lean_object* v_x_1613_ = stack[3].m_obj;
lean_object* v_x_1614_ = stack[4].m_obj;
lean_object* v_res_1681_;
v_res_1681_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1610_, v_x_1611_, v_x_1612_, v_x_1613_, v_x_1614_);
stack->m_obj
 = v_res_1681_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(size_t v_depth_1682_, lean_object* v_keys_1683_, lean_object* v_vals_1684_, lean_object* v_i_1685_, lean_object* v_entries_1686_){
_start:
{
lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = lean_array_get_size(v_keys_1683_);
v___x_1688_ = lean_nat_dec_lt(v_i_1685_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_dec(v_i_1685_);
return v_entries_1686_;
}
else
{
lean_object* v_k_1689_; lean_object* v_v_1690_; uint64_t v___x_1691_; size_t v_h_1692_; size_t v___x_1693_; lean_object* v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; size_t v_h_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_k_1689_ = lean_array_fget_borrowed(v_keys_1683_, v_i_1685_);
v_v_1690_ = lean_array_fget_borrowed(v_vals_1684_, v_i_1685_);
v___x_1691_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_k_1689_);
v_h_1692_ = lean_uint64_to_usize(v___x_1691_);
v___x_1693_ = ((size_t)5ULL);
v___x_1694_ = lean_unsigned_to_nat(1u);
v___x_1695_ = ((size_t)1ULL);
v___x_1696_ = lean_usize_sub(v_depth_1682_, v___x_1695_);
v___x_1697_ = lean_usize_mul(v___x_1693_, v___x_1696_);
v_h_1698_ = lean_usize_shift_right(v_h_1692_, v___x_1697_);
v___x_1699_ = lean_nat_add(v_i_1685_, v___x_1694_);
lean_dec(v_i_1685_);
lean_inc(v_v_1690_);
lean_inc(v_k_1689_);
v___x_1700_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_entries_1686_, v_h_1698_, v_depth_1682_, v_k_1689_, v_v_1690_);
v_i_1685_ = v___x_1699_;
v_entries_1686_ = v___x_1700_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1682_ = stack[0].m_num;
lean_object* v_keys_1683_ = stack[1].m_obj;
lean_object* v_vals_1684_ = stack[2].m_obj;
lean_object* v_i_1685_ = stack[3].m_obj;
lean_object* v_entries_1686_ = stack[4].m_obj;
lean_object* v_res_1702_;
v_res_1702_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_1682_, v_keys_1683_, v_vals_1684_, v_i_1685_, v_entries_1686_);
stack->m_obj
 = v_res_1702_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1703_, lean_object* v_keys_1704_, lean_object* v_vals_1705_, lean_object* v_i_1706_, lean_object* v_entries_1707_){
_start:
{
size_t v_depth_boxed_1708_; lean_object* v_res_1709_; 
v_depth_boxed_1708_ = lean_unbox_usize(v_depth_1703_);
lean_dec(v_depth_1703_);
v_res_1709_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1708_, v_keys_1704_, v_vals_1705_, v_i_1706_, v_entries_1707_);
lean_dec_ref(v_vals_1705_);
lean_dec_ref(v_keys_1704_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___boxed(lean_object* v_x_1710_, lean_object* v_x_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_){
_start:
{
size_t v_x_1791__boxed_1715_; size_t v_x_1792__boxed_1716_; lean_object* v_res_1717_; 
v_x_1791__boxed_1715_ = lean_unbox_usize(v_x_1711_);
lean_dec(v_x_1711_);
v_x_1792__boxed_1716_ = lean_unbox_usize(v_x_1712_);
lean_dec(v_x_1712_);
v_res_1717_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1710_, v_x_1791__boxed_1715_, v_x_1792__boxed_1716_, v_x_1713_, v_x_1714_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(lean_object* v_x_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_){
_start:
{
uint64_t v___x_1721_; size_t v___x_1722_; size_t v___x_1723_; lean_object* v___x_1724_; 
v___x_1721_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_1719_);
v___x_1722_ = lean_uint64_to_usize(v___x_1721_);
v___x_1723_ = ((size_t)1ULL);
v___x_1724_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1718_, v___x_1722_, v___x_1723_, v_x_1719_, v_x_1720_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(lean_object* v_old2new_1725_, lean_object* v_x_1726_, lean_object* v_____s_1727_){
_start:
{
lean_object* v_fst_1728_; lean_object* v_snd_1729_; lean_object* v___x_1730_; lean_object* v_m_x27_1731_; lean_object* v___x_1732_; 
v_fst_1728_ = lean_ctor_get(v_x_1726_, 0);
lean_inc(v_fst_1728_);
v_snd_1729_ = lean_ctor_get(v_x_1726_, 1);
lean_inc(v_snd_1729_);
lean_dec_ref(v_x_1726_);
v___x_1730_ = l_Int_Internal_Linear_Poly_reorder(v_fst_1728_, v_old2new_1725_);
v_m_x27_1731_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_____s_1727_, v___x_1730_, v_snd_1729_);
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_m_x27_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed(lean_object* v_old2new_1733_, lean_object* v_x_1734_, lean_object* v_____s_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(v_old2new_1733_, v_x_1734_, v_____s_1735_);
lean_dec_ref(v_old2new_1733_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_f_1737_, lean_object* v_keys_1738_, lean_object* v_vals_1739_, lean_object* v_i_1740_, lean_object* v_acc_1741_){
_start:
{
lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1742_ = lean_array_get_size(v_keys_1738_);
v___x_1743_ = lean_nat_dec_lt(v_i_1740_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
lean_dec(v_i_1740_);
lean_dec_ref(v_f_1737_);
v___x_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_acc_1741_);
return v___x_1744_;
}
else
{
lean_object* v_k_1745_; lean_object* v_v_1746_; lean_object* v___x_1747_; 
v_k_1745_ = lean_array_fget_borrowed(v_keys_1738_, v_i_1740_);
v_v_1746_ = lean_array_fget_borrowed(v_vals_1739_, v_i_1740_);
lean_inc_ref(v_f_1737_);
lean_inc(v_v_1746_);
lean_inc(v_k_1745_);
v___x_1747_ = lean_apply_3(v_f_1737_, v_acc_1741_, v_k_1745_, v_v_1746_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_dec(v_i_1740_);
lean_dec_ref(v_f_1737_);
return v___x_1747_;
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_nat_add(v_i_1740_, v___x_1749_);
lean_dec(v_i_1740_);
v_i_1740_ = v___x_1750_;
v_acc_1741_ = v_a_1748_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_f_1752_, lean_object* v_keys_1753_, lean_object* v_vals_1754_, lean_object* v_i_1755_, lean_object* v_acc_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1752_, v_keys_1753_, v_vals_1754_, v_i_1755_, v_acc_1756_);
lean_dec_ref(v_vals_1754_);
lean_dec_ref(v_keys_1753_);
return v_res_1757_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_f_1758_, lean_object* v_as_1759_, size_t v_i_1760_, size_t v_stop_1761_, lean_object* v_b_1762_){
_start:
{
lean_object* v_a_1764_; lean_object* v___y_1769_; uint8_t v___x_1771_; 
v___x_1771_ = lean_usize_dec_eq(v_i_1760_, v_stop_1761_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_array_uget_borrowed(v_as_1759_, v_i_1760_);
switch(lean_obj_tag(v___x_1772_))
{
case 0:
{
lean_object* v_key_1773_; lean_object* v_val_1774_; lean_object* v___x_1775_; 
v_key_1773_ = lean_ctor_get(v___x_1772_, 0);
v_val_1774_ = lean_ctor_get(v___x_1772_, 1);
lean_inc_ref(v_f_1758_);
lean_inc(v_val_1774_);
lean_inc(v_key_1773_);
v___x_1775_ = lean_apply_3(v_f_1758_, v_b_1762_, v_key_1773_, v_val_1774_);
v___y_1769_ = v___x_1775_;
goto v___jp_1768_;
}
case 1:
{
lean_object* v_node_1776_; lean_object* v___x_1777_; 
v_node_1776_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_node_1776_);
lean_inc_ref(v_f_1758_);
v___x_1777_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1758_, v_node_1776_, v_b_1762_);
v___y_1769_ = v___x_1777_;
goto v___jp_1768_;
}
default: 
{
v_a_1764_ = v_b_1762_;
goto v___jp_1763_;
}
}
}
else
{
lean_object* v___x_1778_; 
lean_dec_ref(v_f_1758_);
v___x_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_b_1762_);
return v___x_1778_;
}
v___jp_1763_:
{
size_t v___x_1765_; size_t v___x_1766_; 
v___x_1765_ = ((size_t)1ULL);
v___x_1766_ = lean_usize_add(v_i_1760_, v___x_1765_);
v_i_1760_ = v___x_1766_;
v_b_1762_ = v_a_1764_;
goto _start;
}
v___jp_1768_:
{
if (lean_obj_tag(v___y_1769_) == 0)
{
lean_dec_ref(v_f_1758_);
return v___y_1769_;
}
else
{
lean_object* v_a_1770_; 
v_a_1770_ = lean_ctor_get(v___y_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___y_1769_, 1);
v_a_1764_ = v_a_1770_;
goto v___jp_1763_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1758_ = stack[0].m_obj;
lean_object* v_as_1759_ = stack[1].m_obj;
size_t v_i_1760_ = stack[2].m_num;
size_t v_stop_1761_ = stack[3].m_num;
lean_object* v_b_1762_ = stack[4].m_obj;
lean_object* v_res_1779_;
v_res_1779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1758_, v_as_1759_, v_i_1760_, v_stop_1761_, v_b_1762_);
stack->m_obj
 = v_res_1779_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(lean_object* v_f_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_){
_start:
{
if (lean_obj_tag(v_x_1781_) == 0)
{
lean_object* v_es_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1796_; 
v_es_1783_ = lean_ctor_get(v_x_1781_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_x_1781_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1785_ = v_x_1781_;
v_isShared_1786_ = v_isSharedCheck_1796_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_es_1783_);
lean_dec(v_x_1781_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1796_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = lean_array_get_size(v_es_1783_);
v___x_1789_ = lean_nat_dec_lt(v___x_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1791_; 
lean_dec_ref(v_es_1783_);
lean_dec_ref(v_f_1780_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 1);
lean_ctor_set(v___x_1785_, 0, v_x_1782_);
v___x_1791_ = v___x_1785_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_x_1782_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
else
{
size_t v___x_1793_; size_t v___x_1794_; lean_object* v___x_1795_; 
lean_del_object(v___x_1785_);
v___x_1793_ = ((size_t)0ULL);
v___x_1794_ = lean_usize_of_nat(v___x_1788_);
v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1780_, v_es_1783_, v___x_1793_, v___x_1794_, v_x_1782_);
lean_dec_ref(v_es_1783_);
return v___x_1795_;
}
}
}
else
{
lean_object* v_ks_1797_; lean_object* v_vs_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_ks_1797_ = lean_ctor_get(v_x_1781_, 0);
lean_inc_ref(v_ks_1797_);
v_vs_1798_ = lean_ctor_get(v_x_1781_, 1);
lean_inc_ref(v_vs_1798_);
lean_dec_ref_known(v_x_1781_, 2);
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1800_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1780_, v_ks_1797_, v_vs_1798_, v___x_1799_, v_x_1782_);
lean_dec_ref(v_vs_1798_);
lean_dec_ref(v_ks_1797_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_f_1801_, lean_object* v_as_1802_, lean_object* v_i_1803_, lean_object* v_stop_1804_, lean_object* v_b_1805_){
_start:
{
size_t v_i_boxed_1806_; size_t v_stop_boxed_1807_; lean_object* v_res_1808_; 
v_i_boxed_1806_ = lean_unbox_usize(v_i_1803_);
lean_dec(v_i_1803_);
v_stop_boxed_1807_ = lean_unbox_usize(v_stop_1804_);
lean_dec(v_stop_1804_);
v_res_1808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1801_, v_as_1802_, v_i_boxed_1806_, v_stop_boxed_1807_, v_b_1805_);
lean_dec_ref(v_as_1802_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0(lean_object* v_f_1809_, lean_object* v_s_1810_, lean_object* v_a_1811_, lean_object* v_b_1812_){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v_a_1811_);
lean_ctor_set(v___x_1813_, 1, v_b_1812_);
v___x_1814_ = lean_apply_2(v_f_1809_, v___x_1813_, v_s_1810_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
v_a_1823_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1814_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1814_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(lean_object* v_map_1831_, lean_object* v_init_1832_, lean_object* v_f_1833_){
_start:
{
lean_object* v___f_1834_; lean_object* v___x_1835_; lean_object* v_a_1836_; 
v___f_1834_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1834_, 0, v_f_1833_);
lean_inc_ref(v_map_1831_);
v___x_1835_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v___f_1834_, v_map_1831_, v_init_1832_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref(v___x_1835_);
return v_a_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___boxed(lean_object* v_map_1837_, lean_object* v_init_1838_, lean_object* v_f_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_1837_, v_init_1838_, v_f_1839_);
lean_dec_ref(v_map_1837_);
return v_res_1840_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0(void){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1841_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1(void){
_start:
{
lean_object* v___x_1842_; lean_object* v_m_x27_1843_; 
v___x_1842_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0);
v_m_x27_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_m_x27_1843_, 0, v___x_1842_);
return v_m_x27_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(lean_object* v_m_1844_, lean_object* v_old2new_1845_){
_start:
{
lean_object* v___f_1846_; lean_object* v_m_x27_1847_; lean_object* v___x_1848_; 
v___f_1846_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1846_, 0, v_old2new_1845_);
v_m_x27_1847_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
v___x_1848_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_m_1844_, v_m_x27_1847_, v___f_1846_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___boxed(lean_object* v_m_1849_, lean_object* v_old2new_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(v_m_1849_, v_old2new_1850_);
lean_dec_ref(v_m_1849_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0(lean_object* v_00_u03b2_1852_, lean_object* v_x_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_x_1853_, v_x_1854_, v_x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(lean_object* v_00_u03c3_1857_, lean_object* v_00_u03b2_1858_, lean_object* v_map_1859_, lean_object* v_init_1860_, lean_object* v_f_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_1859_, v_init_1860_, v_f_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___boxed(lean_object* v_00_u03c3_1863_, lean_object* v_00_u03b2_1864_, lean_object* v_map_1865_, lean_object* v_init_1866_, lean_object* v_f_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(v_00_u03c3_1863_, v_00_u03b2_1864_, v_map_1865_, v_init_1866_, v_f_1867_);
lean_dec_ref(v_map_1865_);
return v_res_1868_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(lean_object* v_00_u03b2_1869_, lean_object* v_x_1870_, size_t v_x_1871_, size_t v_x_1872_, lean_object* v_x_1873_, lean_object* v_x_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1870_, v_x_1871_, v_x_1872_, v_x_1873_, v_x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1870_ = stack[1].m_obj;
size_t v_x_1871_ = stack[2].m_num;
size_t v_x_1872_ = stack[3].m_num;
lean_object* v_x_1873_ = stack[4].m_obj;
lean_object* v_x_1874_ = stack[5].m_obj;
lean_object* v_res_1876_;
v_res_1876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(lean_box(0), v_x_1870_, v_x_1871_, v_x_1872_, v_x_1873_, v_x_1874_);
stack->m_obj
 = v_res_1876_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
size_t v_x_2297__boxed_1883_; size_t v_x_2298__boxed_1884_; lean_object* v_res_1885_; 
v_x_2297__boxed_1883_ = lean_unbox_usize(v_x_1879_);
lean_dec(v_x_1879_);
v_x_2298__boxed_1884_ = lean_unbox_usize(v_x_1880_);
lean_dec(v_x_1880_);
v_res_1885_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(v_00_u03b2_1877_, v_x_1878_, v_x_2297__boxed_1883_, v_x_2298__boxed_1884_, v_x_1881_, v_x_1882_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2___redArg(lean_object* v_map_1886_, lean_object* v_f_1887_, lean_object* v_init_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1887_, v_map_1886_, v_init_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2(lean_object* v_00_u03c3_1890_, lean_object* v_00_u03c3_1891_, lean_object* v_00_u03b2_1892_, lean_object* v_map_1893_, lean_object* v_f_1894_, lean_object* v_init_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1894_, v_map_1893_, v_init_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1897_, lean_object* v_n_1898_, lean_object* v_k_1899_, lean_object* v_v_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v_n_1898_, v_k_1899_, v_v_1900_);
return v___x_1901_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1902_, size_t v_depth_1903_, lean_object* v_keys_1904_, lean_object* v_vals_1905_, lean_object* v_heq_1906_, lean_object* v_i_1907_, lean_object* v_entries_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_1903_, v_keys_1904_, v_vals_1905_, v_i_1907_, v_entries_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1903_ = stack[1].m_num;
lean_object* v_keys_1904_ = stack[2].m_obj;
lean_object* v_vals_1905_ = stack[3].m_obj;
lean_object* v_i_1907_ = stack[5].m_obj;
lean_object* v_entries_1908_ = stack[6].m_obj;
lean_object* v_res_1910_;
v_res_1910_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(lean_box(0), v_depth_1903_, v_keys_1904_, v_vals_1905_, lean_box(0), v_i_1907_, v_entries_1908_);
stack->m_obj
 = v_res_1910_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1911_, lean_object* v_depth_1912_, lean_object* v_keys_1913_, lean_object* v_vals_1914_, lean_object* v_heq_1915_, lean_object* v_i_1916_, lean_object* v_entries_1917_){
_start:
{
size_t v_depth_boxed_1918_; lean_object* v_res_1919_; 
v_depth_boxed_1918_ = lean_unbox_usize(v_depth_1912_);
lean_dec(v_depth_1912_);
v_res_1919_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(v_00_u03b2_1911_, v_depth_boxed_1918_, v_keys_1913_, v_vals_1914_, v_heq_1915_, v_i_1916_, v_entries_1917_);
lean_dec_ref(v_vals_1914_);
lean_dec_ref(v_keys_1913_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5(lean_object* v_00_u03c3_1920_, lean_object* v_00_u03c3_1921_, lean_object* v_00_u03b1_1922_, lean_object* v_00_u03b2_1923_, lean_object* v_f_1924_, lean_object* v_x_1925_, lean_object* v_x_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1924_, v_x_1925_, v_x_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1928_, lean_object* v_x_1929_, lean_object* v_x_1930_, lean_object* v_x_1931_, lean_object* v_x_1932_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1929_, v_x_1930_, v_x_1931_, v_x_1932_);
return v___x_1933_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_1934_, lean_object* v_00_u03b2_1935_, lean_object* v_00_u03c3_1936_, lean_object* v_00_u03c3_1937_, lean_object* v_f_1938_, lean_object* v_as_1939_, size_t v_i_1940_, size_t v_stop_1941_, lean_object* v_b_1942_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1938_, v_as_1939_, v_i_1940_, v_stop_1941_, v_b_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1938_ = stack[4].m_obj;
lean_object* v_as_1939_ = stack[5].m_obj;
size_t v_i_1940_ = stack[6].m_num;
size_t v_stop_1941_ = stack[7].m_num;
lean_object* v_b_1942_ = stack[8].m_obj;
lean_object* v_res_1944_;
v_res_1944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_f_1938_, v_as_1939_, v_i_1940_, v_stop_1941_, v_b_1942_);
stack->m_obj
 = v_res_1944_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1945_, lean_object* v_00_u03b2_1946_, lean_object* v_00_u03c3_1947_, lean_object* v_00_u03c3_1948_, lean_object* v_f_1949_, lean_object* v_as_1950_, lean_object* v_i_1951_, lean_object* v_stop_1952_, lean_object* v_b_1953_){
_start:
{
size_t v_i_boxed_1954_; size_t v_stop_boxed_1955_; lean_object* v_res_1956_; 
v_i_boxed_1954_ = lean_unbox_usize(v_i_1951_);
lean_dec(v_i_1951_);
v_stop_boxed_1955_ = lean_unbox_usize(v_stop_1952_);
lean_dec(v_stop_1952_);
v_res_1956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_1945_, v_00_u03b2_1946_, v_00_u03c3_1947_, v_00_u03c3_1948_, v_f_1949_, v_as_1950_, v_i_boxed_1954_, v_stop_boxed_1955_, v_b_1953_);
lean_dec_ref(v_as_1950_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03c3_1957_, lean_object* v_00_u03c3_1958_, lean_object* v_00_u03b1_1959_, lean_object* v_00_u03b2_1960_, lean_object* v_f_1961_, lean_object* v_keys_1962_, lean_object* v_vals_1963_, lean_object* v_heq_1964_, lean_object* v_i_1965_, lean_object* v_acc_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1961_, v_keys_1962_, v_vals_1963_, v_i_1965_, v_acc_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03c3_1968_, lean_object* v_00_u03c3_1969_, lean_object* v_00_u03b1_1970_, lean_object* v_00_u03b2_1971_, lean_object* v_f_1972_, lean_object* v_keys_1973_, lean_object* v_vals_1974_, lean_object* v_heq_1975_, lean_object* v_i_1976_, lean_object* v_acc_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(v_00_u03c3_1968_, v_00_u03c3_1969_, v_00_u03b1_1970_, v_00_u03b2_1971_, v_f_1972_, v_keys_1973_, v_vals_1974_, v_heq_1975_, v_i_1976_, v_acc_1977_);
lean_dec_ref(v_vals_1974_);
lean_dec_ref(v_keys_1973_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object* v___x_1979_, lean_object* v___x_1980_, lean_object* v_x_1981_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_array_get_borrowed(v___x_1979_, v___x_1980_, v_x_1981_);
lean_inc(v___x_1982_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object* v___x_1983_, lean_object* v___x_1984_, lean_object* v_x_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(v___x_1983_, v___x_1984_, v_x_1985_);
lean_dec(v_x_1985_);
lean_dec_ref(v___x_1984_);
lean_dec(v___x_1983_);
return v_res_1986_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(lean_object* v___x_1987_, size_t v_sz_1988_, size_t v_i_1989_, lean_object* v_bs_1990_){
_start:
{
uint8_t v___x_1991_; 
v___x_1991_ = lean_usize_dec_lt(v_i_1989_, v_sz_1988_);
if (v___x_1991_ == 0)
{
return v_bs_1990_;
}
else
{
lean_object* v_v_1992_; lean_object* v___x_1993_; lean_object* v_bs_x27_1994_; lean_object* v___y_1996_; 
v_v_1992_ = lean_array_uget(v_bs_1990_, v_i_1989_);
v___x_1993_ = lean_unsigned_to_nat(0u);
v_bs_x27_1994_ = lean_array_uset(v_bs_1990_, v_i_1989_, v___x_1993_);
if (lean_obj_tag(v_v_1992_) == 0)
{
v___y_1996_ = v_v_1992_;
goto v___jp_1995_;
}
else
{
lean_object* v_val_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2009_; 
v_val_2001_ = lean_ctor_get(v_v_1992_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_v_1992_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2003_ = v_v_1992_;
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_val_2001_);
lean_dec(v_v_1992_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_val_2001_, v___x_1987_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2005_);
v___x_2007_ = v___x_2003_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
v___y_1996_ = v___x_2007_;
goto v___jp_1995_;
}
}
}
v___jp_1995_:
{
size_t v___x_1997_; size_t v___x_1998_; lean_object* v___x_1999_; 
v___x_1997_ = ((size_t)1ULL);
v___x_1998_ = lean_usize_add(v_i_1989_, v___x_1997_);
v___x_1999_ = lean_array_uset(v_bs_x27_1994_, v_i_1989_, v___y_1996_);
v_i_1989_ = v___x_1998_;
v_bs_1990_ = v___x_1999_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1987_ = stack[0].m_obj;
size_t v_sz_1988_ = stack[1].m_num;
size_t v_i_1989_ = stack[2].m_num;
lean_object* v_bs_1990_ = stack[3].m_obj;
lean_object* v_res_2010_;
v_res_2010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(v___x_1987_, v_sz_1988_, v_i_1989_, v_bs_1990_);
stack->m_obj
 = v_res_2010_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13___boxed(lean_object* v___x_2011_, lean_object* v_sz_2012_, lean_object* v_i_2013_, lean_object* v_bs_2014_){
_start:
{
size_t v_sz_boxed_2015_; size_t v_i_boxed_2016_; lean_object* v_res_2017_; 
v_sz_boxed_2015_ = lean_unbox_usize(v_sz_2012_);
lean_dec(v_sz_2012_);
v_i_boxed_2016_ = lean_unbox_usize(v_i_2013_);
lean_dec(v_i_2013_);
v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(v___x_2011_, v_sz_boxed_2015_, v_i_boxed_2016_, v_bs_2014_);
lean_dec_ref(v___x_2011_);
return v_res_2017_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17(lean_object* v___x_2018_, size_t v_sz_2019_, size_t v_i_2020_, lean_object* v_bs_2021_){
_start:
{
uint8_t v___x_2022_; 
v___x_2022_ = lean_usize_dec_lt(v_i_2020_, v_sz_2019_);
if (v___x_2022_ == 0)
{
return v_bs_2021_;
}
else
{
lean_object* v_v_2023_; lean_object* v___x_2024_; lean_object* v_bs_x27_2025_; lean_object* v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; lean_object* v___x_2029_; 
v_v_2023_ = lean_array_uget(v_bs_2021_, v_i_2020_);
v___x_2024_ = lean_unsigned_to_nat(0u);
v_bs_x27_2025_ = lean_array_uset(v_bs_2021_, v_i_2020_, v___x_2024_);
v___x_2026_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v___x_2018_, v_v_2023_);
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_add(v_i_2020_, v___x_2027_);
v___x_2029_ = lean_array_uset(v_bs_x27_2025_, v_i_2020_, v___x_2026_);
v_i_2020_ = v___x_2028_;
v_bs_2021_ = v___x_2029_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2018_ = stack[0].m_obj;
size_t v_sz_2019_ = stack[1].m_num;
size_t v_i_2020_ = stack[2].m_num;
lean_object* v_bs_2021_ = stack[3].m_obj;
lean_object* v_res_2031_;
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17(v___x_2018_, v_sz_2019_, v_i_2020_, v_bs_2021_);
stack->m_obj
 = v_res_2031_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(lean_object* v___x_2032_, lean_object* v_x_2033_){
_start:
{
if (lean_obj_tag(v_x_2033_) == 0)
{
lean_object* v_cs_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2044_; 
v_cs_2034_ = lean_ctor_get(v_x_2033_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_x_2033_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2036_ = v_x_2033_;
v_isShared_2037_ = v_isSharedCheck_2044_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_cs_2034_);
lean_dec(v_x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2044_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
size_t v_sz_2038_; size_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
v_sz_2038_ = lean_array_size(v_cs_2034_);
v___x_2039_ = ((size_t)0ULL);
v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17(v___x_2032_, v_sz_2038_, v___x_2039_, v_cs_2034_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2040_);
v___x_2042_ = v___x_2036_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
else
{
lean_object* v_vs_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2055_; 
v_vs_2045_ = lean_ctor_get(v_x_2033_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_x_2033_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2047_ = v_x_2033_;
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_vs_2045_);
lean_dec(v_x_2033_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
size_t v_sz_2049_; size_t v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
v_sz_2049_ = lean_array_size(v_vs_2045_);
v___x_2050_ = ((size_t)0ULL);
v___x_2051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(v___x_2032_, v_sz_2049_, v___x_2050_, v_vs_2045_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2051_);
v___x_2053_ = v___x_2047_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12___boxed(lean_object* v___x_2056_, lean_object* v_x_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v___x_2056_, v_x_2057_);
lean_dec_ref(v___x_2056_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17___boxed(lean_object* v___x_2059_, lean_object* v_sz_2060_, lean_object* v_i_2061_, lean_object* v_bs_2062_){
_start:
{
size_t v_sz_boxed_2063_; size_t v_i_boxed_2064_; lean_object* v_res_2065_; 
v_sz_boxed_2063_ = lean_unbox_usize(v_sz_2060_);
lean_dec(v_sz_2060_);
v_i_boxed_2064_ = lean_unbox_usize(v_i_2061_);
lean_dec(v_i_2061_);
v_res_2065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12_spec__17(v___x_2059_, v_sz_boxed_2063_, v_i_boxed_2064_, v_bs_2062_);
lean_dec_ref(v___x_2059_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object* v___x_2066_, lean_object* v_t_2067_){
_start:
{
lean_object* v_root_2068_; lean_object* v_tail_2069_; lean_object* v_size_2070_; size_t v_shift_2071_; lean_object* v_tailOff_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2083_; 
v_root_2068_ = lean_ctor_get(v_t_2067_, 0);
v_tail_2069_ = lean_ctor_get(v_t_2067_, 1);
v_size_2070_ = lean_ctor_get(v_t_2067_, 2);
v_shift_2071_ = lean_ctor_get_usize(v_t_2067_, 4);
v_tailOff_2072_ = lean_ctor_get(v_t_2067_, 3);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_t_2067_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2074_ = v_t_2067_;
v_isShared_2075_ = v_isSharedCheck_2083_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_tailOff_2072_);
lean_inc(v_size_2070_);
lean_inc(v_tail_2069_);
lean_inc(v_root_2068_);
lean_dec(v_t_2067_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2083_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; size_t v_sz_2077_; size_t v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2076_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__12(v___x_2066_, v_root_2068_);
v_sz_2077_ = lean_array_size(v_tail_2069_);
v___x_2078_ = ((size_t)0ULL);
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5_spec__13(v___x_2066_, v_sz_2077_, v___x_2078_, v_tail_2069_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 1, v___x_2079_);
lean_ctor_set(v___x_2074_, 0, v___x_2076_);
v___x_2081_ = v___x_2074_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___x_2079_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_size_2070_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v_tailOff_2072_);
lean_ctor_set_usize(v_reuseFailAlloc_2082_, 4, v_shift_2071_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object* v___x_2084_, lean_object* v_t_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2084_, v_t_2085_);
lean_dec_ref(v___x_2084_);
return v_res_2086_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(size_t v_sz_2087_, size_t v_i_2088_, lean_object* v_bs_2089_){
_start:
{
uint8_t v___x_2090_; 
v___x_2090_ = lean_usize_dec_lt(v_i_2088_, v_sz_2087_);
if (v___x_2090_ == 0)
{
return v_bs_2089_;
}
else
{
lean_object* v___x_2091_; lean_object* v_bs_x27_2092_; lean_object* v___x_2093_; size_t v___x_2094_; size_t v___x_2095_; lean_object* v___x_2096_; 
v___x_2091_ = lean_unsigned_to_nat(0u);
v_bs_x27_2092_ = lean_array_uset(v_bs_2089_, v_i_2088_, v___x_2091_);
v___x_2093_ = lean_box(1);
v___x_2094_ = ((size_t)1ULL);
v___x_2095_ = lean_usize_add(v_i_2088_, v___x_2094_);
v___x_2096_ = lean_array_uset(v_bs_x27_2092_, v_i_2088_, v___x_2093_);
v_i_2088_ = v___x_2095_;
v_bs_2089_ = v___x_2096_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2087_ = stack[0].m_num;
size_t v_i_2088_ = stack[1].m_num;
lean_object* v_bs_2089_ = stack[2].m_obj;
lean_object* v_res_2098_;
v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(v_sz_2087_, v_i_2088_, v_bs_2089_);
stack->m_obj
 = v_res_2098_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17___boxed(lean_object* v_sz_2099_, lean_object* v_i_2100_, lean_object* v_bs_2101_){
_start:
{
size_t v_sz_boxed_2102_; size_t v_i_boxed_2103_; lean_object* v_res_2104_; 
v_sz_boxed_2102_ = lean_unbox_usize(v_sz_2099_);
lean_dec(v_sz_2099_);
v_i_boxed_2103_ = lean_unbox_usize(v_i_2100_);
lean_dec(v_i_2100_);
v_res_2104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(v_sz_boxed_2102_, v_i_boxed_2103_, v_bs_2101_);
return v_res_2104_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22(size_t v_sz_2105_, size_t v_i_2106_, lean_object* v_bs_2107_){
_start:
{
uint8_t v___x_2108_; 
v___x_2108_ = lean_usize_dec_lt(v_i_2106_, v_sz_2105_);
if (v___x_2108_ == 0)
{
return v_bs_2107_;
}
else
{
lean_object* v_v_2109_; lean_object* v___x_2110_; lean_object* v_bs_x27_2111_; lean_object* v___x_2112_; size_t v___x_2113_; size_t v___x_2114_; lean_object* v___x_2115_; 
v_v_2109_ = lean_array_uget(v_bs_2107_, v_i_2106_);
v___x_2110_ = lean_unsigned_to_nat(0u);
v_bs_x27_2111_ = lean_array_uset(v_bs_2107_, v_i_2106_, v___x_2110_);
v___x_2112_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16(v_v_2109_);
v___x_2113_ = ((size_t)1ULL);
v___x_2114_ = lean_usize_add(v_i_2106_, v___x_2113_);
v___x_2115_ = lean_array_uset(v_bs_x27_2111_, v_i_2106_, v___x_2112_);
v_i_2106_ = v___x_2114_;
v_bs_2107_ = v___x_2115_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2105_ = stack[0].m_num;
size_t v_i_2106_ = stack[1].m_num;
lean_object* v_bs_2107_ = stack[2].m_obj;
lean_object* v_res_2117_;
v_res_2117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22(v_sz_2105_, v_i_2106_, v_bs_2107_);
stack->m_obj
 = v_res_2117_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16(lean_object* v_x_2118_){
_start:
{
if (lean_obj_tag(v_x_2118_) == 0)
{
lean_object* v_cs_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2129_; 
v_cs_2119_ = lean_ctor_get(v_x_2118_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_x_2118_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2121_ = v_x_2118_;
v_isShared_2122_ = v_isSharedCheck_2129_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_cs_2119_);
lean_dec(v_x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2129_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
size_t v_sz_2123_; size_t v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2127_; 
v_sz_2123_ = lean_array_size(v_cs_2119_);
v___x_2124_ = ((size_t)0ULL);
v___x_2125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22(v_sz_2123_, v___x_2124_, v_cs_2119_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2125_);
v___x_2127_ = v___x_2121_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
else
{
lean_object* v_vs_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2140_; 
v_vs_2130_ = lean_ctor_get(v_x_2118_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_x_2118_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2132_ = v_x_2118_;
v_isShared_2133_ = v_isSharedCheck_2140_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_vs_2130_);
lean_dec(v_x_2118_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2140_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
size_t v_sz_2134_; size_t v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
v_sz_2134_ = lean_array_size(v_vs_2130_);
v___x_2135_ = ((size_t)0ULL);
v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(v_sz_2134_, v___x_2135_, v_vs_2130_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2136_);
v___x_2138_ = v___x_2132_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22___boxed(lean_object* v_sz_2141_, lean_object* v_i_2142_, lean_object* v_bs_2143_){
_start:
{
size_t v_sz_boxed_2144_; size_t v_i_boxed_2145_; lean_object* v_res_2146_; 
v_sz_boxed_2144_ = lean_unbox_usize(v_sz_2141_);
lean_dec(v_sz_2141_);
v_i_boxed_2145_ = lean_unbox_usize(v_i_2142_);
lean_dec(v_i_2142_);
v_res_2146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16_spec__22(v_sz_boxed_2144_, v_i_boxed_2145_, v_bs_2143_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object* v_t_2147_){
_start:
{
lean_object* v_root_2148_; lean_object* v_tail_2149_; lean_object* v_size_2150_; size_t v_shift_2151_; lean_object* v_tailOff_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2163_; 
v_root_2148_ = lean_ctor_get(v_t_2147_, 0);
v_tail_2149_ = lean_ctor_get(v_t_2147_, 1);
v_size_2150_ = lean_ctor_get(v_t_2147_, 2);
v_shift_2151_ = lean_ctor_get_usize(v_t_2147_, 4);
v_tailOff_2152_ = lean_ctor_get(v_t_2147_, 3);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_t_2147_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2154_ = v_t_2147_;
v_isShared_2155_ = v_isSharedCheck_2163_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_tailOff_2152_);
lean_inc(v_size_2150_);
lean_inc(v_tail_2149_);
lean_inc(v_root_2148_);
lean_dec(v_t_2147_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2163_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; size_t v_sz_2157_; size_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2156_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__16(v_root_2148_);
v_sz_2157_ = lean_array_size(v_tail_2149_);
v___x_2158_ = ((size_t)0ULL);
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__17(v_sz_2157_, v___x_2158_, v_tail_2149_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v___x_2159_);
lean_ctor_set(v___x_2154_, 0, v___x_2156_);
v___x_2161_ = v___x_2154_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_size_2150_);
lean_ctor_set(v_reuseFailAlloc_2162_, 3, v_tailOff_2152_);
lean_ctor_set_usize(v_reuseFailAlloc_2162_, 4, v_shift_2151_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object* v___x_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
if (lean_obj_tag(v_a_2165_) == 0)
{
lean_object* v___x_2167_; 
v___x_2167_ = l_List_reverse___redArg(v_a_2166_);
return v___x_2167_;
}
else
{
lean_object* v_head_2168_; lean_object* v_tail_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2179_; 
v_head_2168_ = lean_ctor_get(v_a_2165_, 0);
v_tail_2169_ = lean_ctor_get(v_a_2165_, 1);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_a_2165_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2171_ = v_a_2165_;
v_isShared_2172_ = v_isSharedCheck_2179_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_tail_2169_);
lean_inc(v_head_2168_);
lean_dec(v_a_2165_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2179_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2173_ = lean_unsigned_to_nat(0u);
v___x_2174_ = lean_array_get_borrowed(v___x_2173_, v___x_2164_, v_head_2168_);
lean_dec(v_head_2168_);
lean_inc(v___x_2174_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 1, v_a_2166_);
lean_ctor_set(v___x_2171_, 0, v___x_2174_);
v___x_2176_ = v___x_2171_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_a_2166_);
v___x_2176_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
v_a_2165_ = v_tail_2169_;
v_a_2166_ = v___x_2176_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6___boxed(lean_object* v___x_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(v___x_2180_, v_a_2181_, v_a_2182_);
lean_dec_ref(v___x_2180_);
return v_res_2183_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = lean_unsigned_to_nat(32u);
v___x_2185_ = lean_mk_empty_array_with_capacity(v___x_2184_);
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
return v___x_2186_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1(void){
_start:
{
size_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2187_ = ((size_t)5ULL);
v___x_2188_ = lean_unsigned_to_nat(0u);
v___x_2189_ = lean_unsigned_to_nat(32u);
v___x_2190_ = lean_mk_empty_array_with_capacity(v___x_2189_);
v___x_2191_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__0);
v___x_2192_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v___x_2190_);
lean_ctor_set(v___x_2192_, 2, v___x_2188_);
lean_ctor_set(v___x_2192_, 3, v___x_2188_);
lean_ctor_set_usize(v___x_2192_, 4, v___x_2187_);
return v___x_2192_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(size_t v_sz_2193_, size_t v_i_2194_, lean_object* v_bs_2195_){
_start:
{
uint8_t v___x_2196_; 
v___x_2196_ = lean_usize_dec_lt(v_i_2194_, v_sz_2193_);
if (v___x_2196_ == 0)
{
return v_bs_2195_;
}
else
{
lean_object* v___x_2197_; lean_object* v_bs_x27_2198_; lean_object* v___x_2199_; size_t v___x_2200_; size_t v___x_2201_; lean_object* v___x_2202_; 
v___x_2197_ = lean_unsigned_to_nat(0u);
v_bs_x27_2198_ = lean_array_uset(v_bs_2195_, v_i_2194_, v___x_2197_);
v___x_2199_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___closed__1);
v___x_2200_ = ((size_t)1ULL);
v___x_2201_ = lean_usize_add(v_i_2194_, v___x_2200_);
v___x_2202_ = lean_array_uset(v_bs_x27_2198_, v_i_2194_, v___x_2199_);
v_i_2194_ = v___x_2201_;
v_bs_2195_ = v___x_2202_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2193_ = stack[0].m_num;
size_t v_i_2194_ = stack[1].m_num;
lean_object* v_bs_2195_ = stack[2].m_obj;
lean_object* v_res_2204_;
v_res_2204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(v_sz_2193_, v_i_2194_, v_bs_2195_);
stack->m_obj
 = v_res_2204_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10___boxed(lean_object* v_sz_2205_, lean_object* v_i_2206_, lean_object* v_bs_2207_){
_start:
{
size_t v_sz_boxed_2208_; size_t v_i_boxed_2209_; lean_object* v_res_2210_; 
v_sz_boxed_2208_ = lean_unbox_usize(v_sz_2205_);
lean_dec(v_sz_2205_);
v_i_boxed_2209_ = lean_unbox_usize(v_i_2206_);
lean_dec(v_i_2206_);
v_res_2210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(v_sz_boxed_2208_, v_i_boxed_2209_, v_bs_2207_);
return v_res_2210_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13(size_t v_sz_2211_, size_t v_i_2212_, lean_object* v_bs_2213_){
_start:
{
uint8_t v___x_2214_; 
v___x_2214_ = lean_usize_dec_lt(v_i_2212_, v_sz_2211_);
if (v___x_2214_ == 0)
{
return v_bs_2213_;
}
else
{
lean_object* v_v_2215_; lean_object* v___x_2216_; lean_object* v_bs_x27_2217_; lean_object* v___x_2218_; size_t v___x_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
v_v_2215_ = lean_array_uget(v_bs_2213_, v_i_2212_);
v___x_2216_ = lean_unsigned_to_nat(0u);
v_bs_x27_2217_ = lean_array_uset(v_bs_2213_, v_i_2212_, v___x_2216_);
v___x_2218_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9(v_v_2215_);
v___x_2219_ = ((size_t)1ULL);
v___x_2220_ = lean_usize_add(v_i_2212_, v___x_2219_);
v___x_2221_ = lean_array_uset(v_bs_x27_2217_, v_i_2212_, v___x_2218_);
v_i_2212_ = v___x_2220_;
v_bs_2213_ = v___x_2221_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2211_ = stack[0].m_num;
size_t v_i_2212_ = stack[1].m_num;
lean_object* v_bs_2213_ = stack[2].m_obj;
lean_object* v_res_2223_;
v_res_2223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13(v_sz_2211_, v_i_2212_, v_bs_2213_);
stack->m_obj
 = v_res_2223_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9(lean_object* v_x_2224_){
_start:
{
if (lean_obj_tag(v_x_2224_) == 0)
{
lean_object* v_cs_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2235_; 
v_cs_2225_ = lean_ctor_get(v_x_2224_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_x_2224_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2227_ = v_x_2224_;
v_isShared_2228_ = v_isSharedCheck_2235_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_cs_2225_);
lean_dec(v_x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2235_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
size_t v_sz_2229_; size_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v_sz_2229_ = lean_array_size(v_cs_2225_);
v___x_2230_ = ((size_t)0ULL);
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13(v_sz_2229_, v___x_2230_, v_cs_2225_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2231_);
v___x_2233_ = v___x_2227_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
else
{
lean_object* v_vs_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2246_; 
v_vs_2236_ = lean_ctor_get(v_x_2224_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_x_2224_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2238_ = v_x_2224_;
v_isShared_2239_ = v_isSharedCheck_2246_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_vs_2236_);
lean_dec(v_x_2224_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2246_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
size_t v_sz_2240_; size_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2244_; 
v_sz_2240_ = lean_array_size(v_vs_2236_);
v___x_2241_ = ((size_t)0ULL);
v___x_2242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(v_sz_2240_, v___x_2241_, v_vs_2236_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2242_);
v___x_2244_ = v___x_2238_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13___boxed(lean_object* v_sz_2247_, lean_object* v_i_2248_, lean_object* v_bs_2249_){
_start:
{
size_t v_sz_boxed_2250_; size_t v_i_boxed_2251_; lean_object* v_res_2252_; 
v_sz_boxed_2250_ = lean_unbox_usize(v_sz_2247_);
lean_dec(v_sz_2247_);
v_i_boxed_2251_ = lean_unbox_usize(v_i_2248_);
lean_dec(v_i_2248_);
v_res_2252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9_spec__13(v_sz_boxed_2250_, v_i_boxed_2251_, v_bs_2249_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object* v_t_2253_){
_start:
{
lean_object* v_root_2254_; lean_object* v_tail_2255_; lean_object* v_size_2256_; size_t v_shift_2257_; lean_object* v_tailOff_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2269_; 
v_root_2254_ = lean_ctor_get(v_t_2253_, 0);
v_tail_2255_ = lean_ctor_get(v_t_2253_, 1);
v_size_2256_ = lean_ctor_get(v_t_2253_, 2);
v_shift_2257_ = lean_ctor_get_usize(v_t_2253_, 4);
v_tailOff_2258_ = lean_ctor_get(v_t_2253_, 3);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_t_2253_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2260_ = v_t_2253_;
v_isShared_2261_ = v_isSharedCheck_2269_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_tailOff_2258_);
lean_inc(v_size_2256_);
lean_inc(v_tail_2255_);
lean_inc(v_root_2254_);
lean_dec(v_t_2253_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2269_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; size_t v_sz_2263_; size_t v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2262_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__9(v_root_2254_);
v_sz_2263_ = lean_array_size(v_tail_2255_);
v___x_2264_ = ((size_t)0ULL);
v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__10(v_sz_2263_, v___x_2264_, v_tail_2255_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 1, v___x_2265_);
lean_ctor_set(v___x_2260_, 0, v___x_2262_);
v___x_2267_ = v___x_2260_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2268_, 2, v_size_2256_);
lean_ctor_set(v_reuseFailAlloc_2268_, 3, v_tailOff_2258_);
lean_ctor_set_usize(v_reuseFailAlloc_2268_, 4, v_shift_2257_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = lean_unsigned_to_nat(32u);
v___x_2271_ = lean_mk_empty_array_with_capacity(v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
return v___x_2272_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1(void){
_start:
{
size_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2273_ = ((size_t)5ULL);
v___x_2274_ = lean_unsigned_to_nat(0u);
v___x_2275_ = lean_unsigned_to_nat(32u);
v___x_2276_ = lean_mk_empty_array_with_capacity(v___x_2275_);
v___x_2277_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__0);
v___x_2278_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v___x_2276_);
lean_ctor_set(v___x_2278_, 2, v___x_2274_);
lean_ctor_set(v___x_2278_, 3, v___x_2274_);
lean_ctor_set_usize(v___x_2278_, 4, v___x_2273_);
return v___x_2278_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(size_t v_sz_2279_, size_t v_i_2280_, lean_object* v_bs_2281_){
_start:
{
uint8_t v___x_2282_; 
v___x_2282_ = lean_usize_dec_lt(v_i_2280_, v_sz_2279_);
if (v___x_2282_ == 0)
{
return v_bs_2281_;
}
else
{
lean_object* v___x_2283_; lean_object* v_bs_x27_2284_; lean_object* v___x_2285_; size_t v___x_2286_; size_t v___x_2287_; lean_object* v___x_2288_; 
v___x_2283_ = lean_unsigned_to_nat(0u);
v_bs_x27_2284_ = lean_array_uset(v_bs_2281_, v_i_2280_, v___x_2283_);
v___x_2285_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___closed__1);
v___x_2286_ = ((size_t)1ULL);
v___x_2287_ = lean_usize_add(v_i_2280_, v___x_2286_);
v___x_2288_ = lean_array_uset(v_bs_x27_2284_, v_i_2280_, v___x_2285_);
v_i_2280_ = v___x_2287_;
v_bs_2281_ = v___x_2288_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2279_ = stack[0].m_num;
size_t v_i_2280_ = stack[1].m_num;
lean_object* v_bs_2281_ = stack[2].m_obj;
lean_object* v_res_2290_;
v_res_2290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_sz_2279_, v_i_2280_, v_bs_2281_);
stack->m_obj
 = v_res_2290_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7___boxed(lean_object* v_sz_2291_, lean_object* v_i_2292_, lean_object* v_bs_2293_){
_start:
{
size_t v_sz_boxed_2294_; size_t v_i_boxed_2295_; lean_object* v_res_2296_; 
v_sz_boxed_2294_ = lean_unbox_usize(v_sz_2291_);
lean_dec(v_sz_2291_);
v_i_boxed_2295_ = lean_unbox_usize(v_i_2292_);
lean_dec(v_i_2292_);
v_res_2296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_sz_boxed_2294_, v_i_boxed_2295_, v_bs_2293_);
return v_res_2296_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9(size_t v_sz_2297_, size_t v_i_2298_, lean_object* v_bs_2299_){
_start:
{
uint8_t v___x_2300_; 
v___x_2300_ = lean_usize_dec_lt(v_i_2298_, v_sz_2297_);
if (v___x_2300_ == 0)
{
return v_bs_2299_;
}
else
{
lean_object* v_v_2301_; lean_object* v___x_2302_; lean_object* v_bs_x27_2303_; lean_object* v___x_2304_; size_t v___x_2305_; size_t v___x_2306_; lean_object* v___x_2307_; 
v_v_2301_ = lean_array_uget(v_bs_2299_, v_i_2298_);
v___x_2302_ = lean_unsigned_to_nat(0u);
v_bs_x27_2303_ = lean_array_uset(v_bs_2299_, v_i_2298_, v___x_2302_);
v___x_2304_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(v_v_2301_);
v___x_2305_ = ((size_t)1ULL);
v___x_2306_ = lean_usize_add(v_i_2298_, v___x_2305_);
v___x_2307_ = lean_array_uset(v_bs_x27_2303_, v_i_2298_, v___x_2304_);
v_i_2298_ = v___x_2306_;
v_bs_2299_ = v___x_2307_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2297_ = stack[0].m_num;
size_t v_i_2298_ = stack[1].m_num;
lean_object* v_bs_2299_ = stack[2].m_obj;
lean_object* v_res_2309_;
v_res_2309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9(v_sz_2297_, v_i_2298_, v_bs_2299_);
stack->m_obj
 = v_res_2309_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(lean_object* v_x_2310_){
_start:
{
if (lean_obj_tag(v_x_2310_) == 0)
{
lean_object* v_cs_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2321_; 
v_cs_2311_ = lean_ctor_get(v_x_2310_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_x_2310_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2313_ = v_x_2310_;
v_isShared_2314_ = v_isSharedCheck_2321_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_cs_2311_);
lean_dec(v_x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2321_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
size_t v_sz_2315_; size_t v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v_sz_2315_ = lean_array_size(v_cs_2311_);
v___x_2316_ = ((size_t)0ULL);
v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9(v_sz_2315_, v___x_2316_, v_cs_2311_);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2317_);
v___x_2319_ = v___x_2313_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
else
{
lean_object* v_vs_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2332_; 
v_vs_2322_ = lean_ctor_get(v_x_2310_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_x_2310_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2324_ = v_x_2310_;
v_isShared_2325_ = v_isSharedCheck_2332_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_vs_2322_);
lean_dec(v_x_2310_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2332_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
size_t v_sz_2326_; size_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v_sz_2326_ = lean_array_size(v_vs_2322_);
v___x_2327_ = ((size_t)0ULL);
v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_sz_2326_, v___x_2327_, v_vs_2322_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2328_);
v___x_2330_ = v___x_2324_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9___boxed(lean_object* v_sz_2333_, lean_object* v_i_2334_, lean_object* v_bs_2335_){
_start:
{
size_t v_sz_boxed_2336_; size_t v_i_boxed_2337_; lean_object* v_res_2338_; 
v_sz_boxed_2336_ = lean_unbox_usize(v_sz_2333_);
lean_dec(v_sz_2333_);
v_i_boxed_2337_ = lean_unbox_usize(v_i_2334_);
lean_dec(v_i_2334_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6_spec__9(v_sz_boxed_2336_, v_i_boxed_2337_, v_bs_2335_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object* v_t_2339_){
_start:
{
lean_object* v_root_2340_; lean_object* v_tail_2341_; lean_object* v_size_2342_; size_t v_shift_2343_; lean_object* v_tailOff_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2355_; 
v_root_2340_ = lean_ctor_get(v_t_2339_, 0);
v_tail_2341_ = lean_ctor_get(v_t_2339_, 1);
v_size_2342_ = lean_ctor_get(v_t_2339_, 2);
v_shift_2343_ = lean_ctor_get_usize(v_t_2339_, 4);
v_tailOff_2344_ = lean_ctor_get(v_t_2339_, 3);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_t_2339_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2346_ = v_t_2339_;
v_isShared_2347_ = v_isSharedCheck_2355_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_tailOff_2344_);
lean_inc(v_size_2342_);
lean_inc(v_tail_2341_);
lean_inc(v_root_2340_);
lean_dec(v_t_2339_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2355_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; size_t v_sz_2349_; size_t v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2348_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__6(v_root_2340_);
v_sz_2349_ = lean_array_size(v_tail_2341_);
v___x_2350_ = ((size_t)0ULL);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__7(v_sz_2349_, v___x_2350_, v_tail_2341_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 1, v___x_2351_);
lean_ctor_set(v___x_2346_, 0, v___x_2348_);
v___x_2353_ = v___x_2346_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2354_, 2, v_size_2342_);
lean_ctor_set(v_reuseFailAlloc_2354_, 3, v_tailOff_2344_);
lean_ctor_set_usize(v_reuseFailAlloc_2354_, 4, v_shift_2343_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(size_t v_sz_2356_, size_t v_i_2357_, lean_object* v_bs_2358_){
_start:
{
uint8_t v___x_2359_; 
v___x_2359_ = lean_usize_dec_lt(v_i_2357_, v_sz_2356_);
if (v___x_2359_ == 0)
{
return v_bs_2358_;
}
else
{
lean_object* v___x_2360_; lean_object* v_bs_x27_2361_; lean_object* v___x_2362_; size_t v___x_2363_; size_t v___x_2364_; lean_object* v___x_2365_; 
v___x_2360_ = lean_unsigned_to_nat(0u);
v_bs_x27_2361_ = lean_array_uset(v_bs_2358_, v_i_2357_, v___x_2360_);
v___x_2362_ = lean_box(0);
v___x_2363_ = ((size_t)1ULL);
v___x_2364_ = lean_usize_add(v_i_2357_, v___x_2363_);
v___x_2365_ = lean_array_uset(v_bs_x27_2361_, v_i_2357_, v___x_2362_);
v_i_2357_ = v___x_2364_;
v_bs_2358_ = v___x_2365_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2356_ = stack[0].m_num;
size_t v_i_2357_ = stack[1].m_num;
lean_object* v_bs_2358_ = stack[2].m_obj;
lean_object* v_res_2367_;
v_res_2367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(v_sz_2356_, v_i_2357_, v_bs_2358_);
stack->m_obj
 = v_res_2367_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4___boxed(lean_object* v_sz_2368_, lean_object* v_i_2369_, lean_object* v_bs_2370_){
_start:
{
size_t v_sz_boxed_2371_; size_t v_i_boxed_2372_; lean_object* v_res_2373_; 
v_sz_boxed_2371_ = lean_unbox_usize(v_sz_2368_);
lean_dec(v_sz_2368_);
v_i_boxed_2372_ = lean_unbox_usize(v_i_2369_);
lean_dec(v_i_2369_);
v_res_2373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(v_sz_boxed_2371_, v_i_boxed_2372_, v_bs_2370_);
return v_res_2373_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5(size_t v_sz_2374_, size_t v_i_2375_, lean_object* v_bs_2376_){
_start:
{
uint8_t v___x_2377_; 
v___x_2377_ = lean_usize_dec_lt(v_i_2375_, v_sz_2374_);
if (v___x_2377_ == 0)
{
return v_bs_2376_;
}
else
{
lean_object* v_v_2378_; lean_object* v___x_2379_; lean_object* v_bs_x27_2380_; lean_object* v___x_2381_; size_t v___x_2382_; size_t v___x_2383_; lean_object* v___x_2384_; 
v_v_2378_ = lean_array_uget(v_bs_2376_, v_i_2375_);
v___x_2379_ = lean_unsigned_to_nat(0u);
v_bs_x27_2380_ = lean_array_uset(v_bs_2376_, v_i_2375_, v___x_2379_);
v___x_2381_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3(v_v_2378_);
v___x_2382_ = ((size_t)1ULL);
v___x_2383_ = lean_usize_add(v_i_2375_, v___x_2382_);
v___x_2384_ = lean_array_uset(v_bs_x27_2380_, v_i_2375_, v___x_2381_);
v_i_2375_ = v___x_2383_;
v_bs_2376_ = v___x_2384_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2374_ = stack[0].m_num;
size_t v_i_2375_ = stack[1].m_num;
lean_object* v_bs_2376_ = stack[2].m_obj;
lean_object* v_res_2386_;
v_res_2386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5(v_sz_2374_, v_i_2375_, v_bs_2376_);
stack->m_obj
 = v_res_2386_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3(lean_object* v_x_2387_){
_start:
{
if (lean_obj_tag(v_x_2387_) == 0)
{
lean_object* v_cs_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2398_; 
v_cs_2388_ = lean_ctor_get(v_x_2387_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_x_2387_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2390_ = v_x_2387_;
v_isShared_2391_ = v_isSharedCheck_2398_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_cs_2388_);
lean_dec(v_x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2398_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
size_t v_sz_2392_; size_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2396_; 
v_sz_2392_ = lean_array_size(v_cs_2388_);
v___x_2393_ = ((size_t)0ULL);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5(v_sz_2392_, v___x_2393_, v_cs_2388_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2394_);
v___x_2396_ = v___x_2390_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
else
{
lean_object* v_vs_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2409_; 
v_vs_2399_ = lean_ctor_get(v_x_2387_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_x_2387_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2401_ = v_x_2387_;
v_isShared_2402_ = v_isSharedCheck_2409_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_vs_2399_);
lean_dec(v_x_2387_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2409_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
size_t v_sz_2403_; size_t v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
v_sz_2403_ = lean_array_size(v_vs_2399_);
v___x_2404_ = ((size_t)0ULL);
v___x_2405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(v_sz_2403_, v___x_2404_, v_vs_2399_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2405_);
v___x_2407_ = v___x_2401_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_2410_, lean_object* v_i_2411_, lean_object* v_bs_2412_){
_start:
{
size_t v_sz_boxed_2413_; size_t v_i_boxed_2414_; lean_object* v_res_2415_; 
v_sz_boxed_2413_ = lean_unbox_usize(v_sz_2410_);
lean_dec(v_sz_2410_);
v_i_boxed_2414_ = lean_unbox_usize(v_i_2411_);
lean_dec(v_i_2411_);
v_res_2415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3_spec__5(v_sz_boxed_2413_, v_i_boxed_2414_, v_bs_2412_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object* v_t_2416_){
_start:
{
lean_object* v_root_2417_; lean_object* v_tail_2418_; lean_object* v_size_2419_; size_t v_shift_2420_; lean_object* v_tailOff_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2432_; 
v_root_2417_ = lean_ctor_get(v_t_2416_, 0);
v_tail_2418_ = lean_ctor_get(v_t_2416_, 1);
v_size_2419_ = lean_ctor_get(v_t_2416_, 2);
v_shift_2420_ = lean_ctor_get_usize(v_t_2416_, 4);
v_tailOff_2421_ = lean_ctor_get(v_t_2416_, 3);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_t_2416_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2423_ = v_t_2416_;
v_isShared_2424_ = v_isSharedCheck_2432_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_tailOff_2421_);
lean_inc(v_size_2419_);
lean_inc(v_tail_2418_);
lean_inc(v_root_2417_);
lean_dec(v_t_2416_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2432_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; size_t v_sz_2426_; size_t v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
v___x_2425_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__3(v_root_2417_);
v_sz_2426_ = lean_array_size(v_tail_2418_);
v___x_2427_ = ((size_t)0ULL);
v___x_2428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__4(v_sz_2426_, v___x_2427_, v_tail_2418_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 1, v___x_2428_);
lean_ctor_set(v___x_2423_, 0, v___x_2425_);
v___x_2430_ = v___x_2423_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v___x_2428_);
lean_ctor_set(v_reuseFailAlloc_2431_, 2, v_size_2419_);
lean_ctor_set(v_reuseFailAlloc_2431_, 3, v_tailOff_2421_);
lean_ctor_set_usize(v_reuseFailAlloc_2431_, 4, v_shift_2420_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(lean_object* v_f_2433_, lean_object* v_as_2434_, lean_object* v_i_2435_, lean_object* v_acc_2436_){
_start:
{
lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2437_ = lean_array_get_size(v_as_2434_);
v___x_2438_ = lean_nat_dec_eq(v_i_2435_, v___x_2437_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2439_ = lean_array_fget_borrowed(v_as_2434_, v_i_2435_);
lean_inc(v_f_2433_);
lean_inc(v___x_2439_);
v___x_2440_ = lean_apply_1(v_f_2433_, v___x_2439_);
v___x_2441_ = lean_unsigned_to_nat(1u);
v___x_2442_ = lean_nat_add(v_i_2435_, v___x_2441_);
lean_dec(v_i_2435_);
v___x_2443_ = lean_array_push(v_acc_2436_, v___x_2440_);
v_i_2435_ = v___x_2442_;
v_acc_2436_ = v___x_2443_;
goto _start;
}
else
{
lean_dec(v_i_2435_);
lean_dec(v_f_2433_);
return v_acc_2436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg___boxed(lean_object* v_f_2445_, lean_object* v_as_2446_, lean_object* v_i_2447_, lean_object* v_acc_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(v_f_2445_, v_as_2446_, v_i_2447_, v_acc_2448_);
lean_dec_ref(v_as_2446_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(lean_object* v_f_2450_, lean_object* v_as_2451_){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2452_ = lean_unsigned_to_nat(0u);
v___x_2453_ = lean_array_get_size(v_as_2451_);
v___x_2454_ = lean_mk_empty_array_with_capacity(v___x_2453_);
v___x_2455_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(v_f_2450_, v_as_2451_, v___x_2452_, v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg___boxed(lean_object* v_f_2456_, lean_object* v_as_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(v_f_2456_, v_as_2457_);
lean_dec_ref(v_as_2457_);
return v_res_2458_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(lean_object* v_f_2459_, size_t v_sz_2460_, size_t v_i_2461_, lean_object* v_bs_2462_){
_start:
{
uint8_t v___x_2463_; 
v___x_2463_ = lean_usize_dec_lt(v_i_2461_, v_sz_2460_);
if (v___x_2463_ == 0)
{
lean_dec(v_f_2459_);
return v_bs_2462_;
}
else
{
lean_object* v_v_2464_; lean_object* v___x_2465_; lean_object* v_bs_x27_2466_; lean_object* v___y_2468_; 
v_v_2464_ = lean_array_uget(v_bs_2462_, v_i_2461_);
v___x_2465_ = lean_unsigned_to_nat(0u);
v_bs_x27_2466_ = lean_array_uset(v_bs_2462_, v_i_2461_, v___x_2465_);
switch(lean_obj_tag(v_v_2464_))
{
case 0:
{
lean_object* v_key_2473_; lean_object* v_val_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2482_; 
v_key_2473_ = lean_ctor_get(v_v_2464_, 0);
v_val_2474_ = lean_ctor_get(v_v_2464_, 1);
v_isSharedCheck_2482_ = !lean_is_exclusive(v_v_2464_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2476_ = v_v_2464_;
v_isShared_2477_ = v_isSharedCheck_2482_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_val_2474_);
lean_inc(v_key_2473_);
lean_dec(v_v_2464_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2482_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; lean_object* v___x_2480_; 
lean_inc(v_f_2459_);
v___x_2478_ = lean_apply_1(v_f_2459_, v_val_2474_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 1, v___x_2478_);
v___x_2480_ = v___x_2476_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_key_2473_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
v___y_2468_ = v___x_2480_;
goto v___jp_2467_;
}
}
}
case 1:
{
lean_object* v_node_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2491_; 
v_node_2483_ = lean_ctor_get(v_v_2464_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v_v_2464_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2485_ = v_v_2464_;
v_isShared_2486_ = v_isSharedCheck_2491_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_node_2483_);
lean_dec(v_v_2464_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2491_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; lean_object* v___x_2489_; 
lean_inc(v_f_2459_);
v___x_2487_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v_f_2459_, v_node_2483_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2487_);
v___x_2489_ = v___x_2485_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
v___y_2468_ = v___x_2489_;
goto v___jp_2467_;
}
}
}
default: 
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_box(2);
v___y_2468_ = v___x_2492_;
goto v___jp_2467_;
}
}
v___jp_2467_:
{
size_t v___x_2469_; size_t v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = ((size_t)1ULL);
v___x_2470_ = lean_usize_add(v_i_2461_, v___x_2469_);
v___x_2471_ = lean_array_uset(v_bs_x27_2466_, v_i_2461_, v___y_2468_);
v_i_2461_ = v___x_2470_;
v_bs_2462_ = v___x_2471_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2459_ = stack[0].m_obj;
size_t v_sz_2460_ = stack[1].m_num;
size_t v_i_2461_ = stack[2].m_num;
lean_object* v_bs_2462_ = stack[3].m_obj;
lean_object* v_res_2493_;
v_res_2493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(v_f_2459_, v_sz_2460_, v_i_2461_, v_bs_2462_);
stack->m_obj
 = v_res_2493_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(lean_object* v_f_2494_, lean_object* v_n_2495_){
_start:
{
if (lean_obj_tag(v_n_2495_) == 0)
{
lean_object* v_es_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2506_; 
v_es_2496_ = lean_ctor_get(v_n_2495_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_n_2495_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2498_ = v_n_2495_;
v_isShared_2499_ = v_isSharedCheck_2506_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_es_2496_);
lean_dec(v_n_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2506_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
size_t v_sz_2500_; size_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; 
v_sz_2500_ = lean_array_size(v_es_2496_);
v___x_2501_ = ((size_t)0ULL);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(v_f_2494_, v_sz_2500_, v___x_2501_, v_es_2496_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2502_);
v___x_2504_ = v___x_2498_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
else
{
lean_object* v_ks_2507_; lean_object* v_vs_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2516_; 
v_ks_2507_ = lean_ctor_get(v_n_2495_, 0);
v_vs_2508_ = lean_ctor_get(v_n_2495_, 1);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_n_2495_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2510_ = v_n_2495_;
v_isShared_2511_ = v_isSharedCheck_2516_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_vs_2508_);
lean_inc(v_ks_2507_);
lean_dec(v_n_2495_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2516_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v_val_2512_; lean_object* v___x_2514_; 
v_val_2512_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(v_f_2494_, v_vs_2508_);
lean_dec_ref(v_vs_2508_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 1, v_val_2512_);
v___x_2514_ = v___x_2510_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_ks_2507_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_val_2512_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg___boxed(lean_object* v_f_2517_, lean_object* v_sz_2518_, lean_object* v_i_2519_, lean_object* v_bs_2520_){
_start:
{
size_t v_sz_boxed_2521_; size_t v_i_boxed_2522_; lean_object* v_res_2523_; 
v_sz_boxed_2521_ = lean_unbox_usize(v_sz_2518_);
lean_dec(v_sz_2518_);
v_i_boxed_2522_ = lean_unbox_usize(v_i_2519_);
lean_dec(v_i_2519_);
v_res_2523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(v_f_2517_, v_sz_boxed_2521_, v_i_boxed_2522_, v_bs_2520_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg___lam__0(lean_object* v_f_2524_, lean_object* v_x_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = lean_apply_1(v_f_2524_, v_x_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(lean_object* v_pm_2527_, lean_object* v_f_2528_){
_start:
{
lean_object* v___f_2529_; lean_object* v___x_2530_; 
v___f_2529_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2529_, 0, v_f_2528_);
v___x_2530_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v___f_2529_, v_pm_2527_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object* v___x_2531_, lean_object* v_a_2532_, lean_object* v___f_2533_, lean_object* v___x_2534_, lean_object* v___x_2535_, lean_object* v_s_2536_){
_start:
{
lean_object* v_vars_2537_; lean_object* v_varMap_2538_; lean_object* v_varsHistory_2539_; lean_object* v_natToIntMap_2540_; lean_object* v_natDef_2541_; lean_object* v_dvds_2542_; lean_object* v_lowers_2543_; lean_object* v_uppers_2544_; lean_object* v_diseqs_2545_; lean_object* v_elimEqs_2546_; lean_object* v_elimStack_2547_; lean_object* v_occurs_2548_; lean_object* v_assignment_2549_; lean_object* v_nextCnstrId_2550_; uint8_t v_caseSplits_2551_; lean_object* v_steps_2552_; lean_object* v_conflict_x3f_2553_; lean_object* v_divMod_2554_; uint8_t v_usedCommRing_2555_; lean_object* v_nonlinearOccs_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2578_; 
v_vars_2537_ = lean_ctor_get(v_s_2536_, 0);
v_varMap_2538_ = lean_ctor_get(v_s_2536_, 1);
v_varsHistory_2539_ = lean_ctor_get(v_s_2536_, 2);
v_natToIntMap_2540_ = lean_ctor_get(v_s_2536_, 3);
v_natDef_2541_ = lean_ctor_get(v_s_2536_, 4);
v_dvds_2542_ = lean_ctor_get(v_s_2536_, 5);
v_lowers_2543_ = lean_ctor_get(v_s_2536_, 6);
v_uppers_2544_ = lean_ctor_get(v_s_2536_, 7);
v_diseqs_2545_ = lean_ctor_get(v_s_2536_, 8);
v_elimEqs_2546_ = lean_ctor_get(v_s_2536_, 9);
v_elimStack_2547_ = lean_ctor_get(v_s_2536_, 10);
v_occurs_2548_ = lean_ctor_get(v_s_2536_, 11);
v_assignment_2549_ = lean_ctor_get(v_s_2536_, 12);
v_nextCnstrId_2550_ = lean_ctor_get(v_s_2536_, 13);
v_caseSplits_2551_ = lean_ctor_get_uint8(v_s_2536_, sizeof(void*)*19);
v_steps_2552_ = lean_ctor_get(v_s_2536_, 14);
v_conflict_x3f_2553_ = lean_ctor_get(v_s_2536_, 15);
v_divMod_2554_ = lean_ctor_get(v_s_2536_, 17);
v_usedCommRing_2555_ = lean_ctor_get_uint8(v_s_2536_, sizeof(void*)*19 + 1);
v_nonlinearOccs_2556_ = lean_ctor_get(v_s_2536_, 18);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_s_2536_);
if (v_isSharedCheck_2578_ == 0)
{
lean_object* v_unused_2579_; 
v_unused_2579_ = lean_ctor_get(v_s_2536_, 16);
lean_dec(v_unused_2579_);
v___x_2558_ = v_s_2536_;
v_isShared_2559_ = v_isSharedCheck_2578_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_nonlinearOccs_2556_);
lean_inc(v_divMod_2554_);
lean_inc(v_conflict_x3f_2553_);
lean_inc(v_steps_2552_);
lean_inc(v_nextCnstrId_2550_);
lean_inc(v_assignment_2549_);
lean_inc(v_occurs_2548_);
lean_inc(v_elimStack_2547_);
lean_inc(v_elimEqs_2546_);
lean_inc(v_diseqs_2545_);
lean_inc(v_uppers_2544_);
lean_inc(v_lowers_2543_);
lean_inc(v_dvds_2542_);
lean_inc(v_natDef_2541_);
lean_inc(v_natToIntMap_2540_);
lean_inc(v_varsHistory_2539_);
lean_inc(v_varMap_2538_);
lean_inc(v_vars_2537_);
lean_dec(v_s_2536_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2578_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
lean_inc_ref(v_a_2532_);
lean_inc_ref(v_vars_2537_);
v___x_2560_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2531_, v_vars_2537_, v_a_2532_);
lean_inc_ref(v___f_2533_);
lean_inc_ref(v_varMap_2538_);
v___x_2561_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(v_varMap_2538_, v___f_2533_);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v_vars_2537_);
lean_ctor_set(v___x_2562_, 1, v_varMap_2538_);
v___x_2563_ = l_Lean_PersistentArray_push___redArg(v_varsHistory_2539_, v___x_2562_);
v___x_2564_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(v_natDef_2541_, v___f_2533_);
v___x_2565_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v_dvds_2542_);
v___x_2566_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_lowers_2543_);
v___x_2567_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_uppers_2544_);
v___x_2568_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v_diseqs_2545_);
v___x_2569_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2534_, v_elimEqs_2546_, v_a_2532_);
v___x_2570_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2535_, v___x_2569_);
v___x_2571_ = lean_box(0);
v___x_2572_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(v___x_2535_, v_elimStack_2547_, v___x_2571_);
v___x_2573_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(v_occurs_2548_);
v___x_2574_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 16, v___x_2574_);
lean_ctor_set(v___x_2558_, 11, v___x_2573_);
lean_ctor_set(v___x_2558_, 10, v___x_2572_);
lean_ctor_set(v___x_2558_, 9, v___x_2570_);
lean_ctor_set(v___x_2558_, 8, v___x_2568_);
lean_ctor_set(v___x_2558_, 7, v___x_2567_);
lean_ctor_set(v___x_2558_, 6, v___x_2566_);
lean_ctor_set(v___x_2558_, 5, v___x_2565_);
lean_ctor_set(v___x_2558_, 4, v___x_2564_);
lean_ctor_set(v___x_2558_, 2, v___x_2563_);
lean_ctor_set(v___x_2558_, 1, v___x_2561_);
lean_ctor_set(v___x_2558_, 0, v___x_2560_);
v___x_2576_ = v___x_2558_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v___x_2561_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v___x_2563_);
lean_ctor_set(v_reuseFailAlloc_2577_, 3, v_natToIntMap_2540_);
lean_ctor_set(v_reuseFailAlloc_2577_, 4, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2577_, 5, v___x_2565_);
lean_ctor_set(v_reuseFailAlloc_2577_, 6, v___x_2566_);
lean_ctor_set(v_reuseFailAlloc_2577_, 7, v___x_2567_);
lean_ctor_set(v_reuseFailAlloc_2577_, 8, v___x_2568_);
lean_ctor_set(v_reuseFailAlloc_2577_, 9, v___x_2570_);
lean_ctor_set(v_reuseFailAlloc_2577_, 10, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2577_, 11, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2577_, 12, v_assignment_2549_);
lean_ctor_set(v_reuseFailAlloc_2577_, 13, v_nextCnstrId_2550_);
lean_ctor_set(v_reuseFailAlloc_2577_, 14, v_steps_2552_);
lean_ctor_set(v_reuseFailAlloc_2577_, 15, v_conflict_x3f_2553_);
lean_ctor_set(v_reuseFailAlloc_2577_, 16, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2577_, 17, v_divMod_2554_);
lean_ctor_set(v_reuseFailAlloc_2577_, 18, v_nonlinearOccs_2556_);
lean_ctor_set_uint8(v_reuseFailAlloc_2577_, sizeof(void*)*19, v_caseSplits_2551_);
lean_ctor_set_uint8(v_reuseFailAlloc_2577_, sizeof(void*)*19 + 1, v_usedCommRing_2555_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object* v___x_2580_, lean_object* v_a_2581_, lean_object* v___f_2582_, lean_object* v___x_2583_, lean_object* v___x_2584_, lean_object* v_s_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(v___x_2580_, v_a_2581_, v___f_2582_, v___x_2583_, v___x_2584_, v_s_2585_);
lean_dec_ref(v___x_2584_);
return v_res_2586_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object* v___x_2587_, size_t v_sz_2588_, size_t v_i_2589_, lean_object* v_bs_2590_){
_start:
{
uint8_t v___x_2591_; 
v___x_2591_ = lean_usize_dec_lt(v_i_2589_, v_sz_2588_);
if (v___x_2591_ == 0)
{
return v_bs_2590_;
}
else
{
lean_object* v_v_2592_; lean_object* v___x_2593_; lean_object* v_bs_x27_2594_; lean_object* v___x_2595_; size_t v___x_2596_; size_t v___x_2597_; lean_object* v___x_2598_; 
v_v_2592_ = lean_array_uget(v_bs_2590_, v_i_2589_);
v___x_2593_ = lean_unsigned_to_nat(0u);
v_bs_x27_2594_ = lean_array_uset(v_bs_2590_, v_i_2589_, v___x_2593_);
v___x_2595_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_v_2592_, v___x_2587_);
v___x_2596_ = ((size_t)1ULL);
v___x_2597_ = lean_usize_add(v_i_2589_, v___x_2596_);
v___x_2598_ = lean_array_uset(v_bs_x27_2594_, v_i_2589_, v___x_2595_);
v_i_2589_ = v___x_2597_;
v_bs_2590_ = v___x_2598_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2587_ = stack[0].m_obj;
size_t v_sz_2588_ = stack[1].m_num;
size_t v_i_2589_ = stack[2].m_num;
lean_object* v_bs_2590_ = stack[3].m_obj;
lean_object* v_res_2600_;
v_res_2600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_2587_, v_sz_2588_, v_i_2589_, v_bs_2590_);
stack->m_obj
 = v_res_2600_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object* v___x_2601_, lean_object* v_sz_2602_, lean_object* v_i_2603_, lean_object* v_bs_2604_){
_start:
{
size_t v_sz_boxed_2605_; size_t v_i_boxed_2606_; lean_object* v_res_2607_; 
v_sz_boxed_2605_ = lean_unbox_usize(v_sz_2602_);
lean_dec(v_sz_2602_);
v_i_boxed_2606_ = lean_unbox_usize(v_i_2603_);
lean_dec(v_i_2603_);
v_res_2607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_2601_, v_sz_boxed_2605_, v_i_boxed_2606_, v_bs_2604_);
lean_dec_ref(v___x_2601_);
return v_res_2607_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(lean_object* v_as_2608_, size_t v_i_2609_, size_t v_stop_2610_, lean_object* v_b_2611_){
_start:
{
lean_object* v___y_2613_; uint8_t v___x_2617_; 
v___x_2617_ = lean_usize_dec_eq(v_i_2609_, v_stop_2610_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_array_uget_borrowed(v_as_2608_, v_i_2609_);
if (lean_obj_tag(v___x_2618_) == 0)
{
v___y_2613_ = v_b_2611_;
goto v___jp_2612_;
}
else
{
lean_object* v_val_2619_; lean_object* v___x_2620_; 
v_val_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_val_2619_);
v___x_2620_ = lean_array_push(v_b_2611_, v_val_2619_);
v___y_2613_ = v___x_2620_;
goto v___jp_2612_;
}
}
else
{
return v_b_2611_;
}
v___jp_2612_:
{
size_t v___x_2614_; size_t v___x_2615_; 
v___x_2614_ = ((size_t)1ULL);
v___x_2615_ = lean_usize_add(v_i_2609_, v___x_2614_);
v_i_2609_ = v___x_2615_;
v_b_2611_ = v___y_2613_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2608_ = stack[0].m_obj;
size_t v_i_2609_ = stack[1].m_num;
size_t v_stop_2610_ = stack[2].m_num;
lean_object* v_b_2611_ = stack[3].m_obj;
lean_object* v_res_2621_;
v_res_2621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_as_2608_, v_i_2609_, v_stop_2610_, v_b_2611_);
stack->m_obj
 = v_res_2621_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20___boxed(lean_object* v_as_2622_, lean_object* v_i_2623_, lean_object* v_stop_2624_, lean_object* v_b_2625_){
_start:
{
size_t v_i_boxed_2626_; size_t v_stop_boxed_2627_; lean_object* v_res_2628_; 
v_i_boxed_2626_ = lean_unbox_usize(v_i_2623_);
lean_dec(v_i_2623_);
v_stop_boxed_2627_ = lean_unbox_usize(v_stop_2624_);
lean_dec(v_stop_2624_);
v_res_2628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_as_2622_, v_i_boxed_2626_, v_stop_boxed_2627_, v_b_2625_);
lean_dec_ref(v_as_2622_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(lean_object* v_x_2629_, lean_object* v_x_2630_){
_start:
{
if (lean_obj_tag(v_x_2629_) == 0)
{
lean_object* v_cs_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v_cs_2631_ = lean_ctor_get(v_x_2629_, 0);
v___x_2632_ = lean_unsigned_to_nat(0u);
v___x_2633_ = lean_array_get_size(v_cs_2631_);
v___x_2634_ = lean_nat_dec_lt(v___x_2632_, v___x_2633_);
if (v___x_2634_ == 0)
{
return v_x_2630_;
}
else
{
size_t v___x_2635_; size_t v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = ((size_t)0ULL);
v___x_2636_ = lean_usize_of_nat(v___x_2633_);
v___x_2637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(v_cs_2631_, v___x_2635_, v___x_2636_, v_x_2630_);
return v___x_2637_;
}
}
else
{
lean_object* v_vs_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; 
v_vs_2638_ = lean_ctor_get(v_x_2629_, 0);
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = lean_array_get_size(v_vs_2638_);
v___x_2641_ = lean_nat_dec_lt(v___x_2639_, v___x_2640_);
if (v___x_2641_ == 0)
{
return v_x_2630_;
}
else
{
size_t v___x_2642_; size_t v___x_2643_; lean_object* v___x_2644_; 
v___x_2642_ = ((size_t)0ULL);
v___x_2643_ = lean_usize_of_nat(v___x_2640_);
v___x_2644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_vs_2638_, v___x_2642_, v___x_2643_, v_x_2630_);
return v___x_2644_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(lean_object* v_as_2645_, size_t v_i_2646_, size_t v_stop_2647_, lean_object* v_b_2648_){
_start:
{
uint8_t v___x_2649_; 
v___x_2649_ = lean_usize_dec_eq(v_i_2646_, v_stop_2647_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; lean_object* v___x_2651_; size_t v___x_2652_; size_t v___x_2653_; 
v___x_2650_ = lean_array_uget_borrowed(v_as_2645_, v_i_2646_);
v___x_2651_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(v___x_2650_, v_b_2648_);
v___x_2652_ = ((size_t)1ULL);
v___x_2653_ = lean_usize_add(v_i_2646_, v___x_2652_);
v_i_2646_ = v___x_2653_;
v_b_2648_ = v___x_2651_;
goto _start;
}
else
{
return v_b_2648_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2645_ = stack[0].m_obj;
size_t v_i_2646_ = stack[1].m_num;
size_t v_stop_2647_ = stack[2].m_num;
lean_object* v_b_2648_ = stack[3].m_obj;
lean_object* v_res_2655_;
v_res_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(v_as_2645_, v_i_2646_, v_stop_2647_, v_b_2648_);
stack->m_obj
 = v_res_2655_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26___boxed(lean_object* v_as_2656_, lean_object* v_i_2657_, lean_object* v_stop_2658_, lean_object* v_b_2659_){
_start:
{
size_t v_i_boxed_2660_; size_t v_stop_boxed_2661_; lean_object* v_res_2662_; 
v_i_boxed_2660_ = lean_unbox_usize(v_i_2657_);
lean_dec(v_i_2657_);
v_stop_boxed_2661_ = lean_unbox_usize(v_stop_2658_);
lean_dec(v_stop_2658_);
v_res_2662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(v_as_2656_, v_i_boxed_2660_, v_stop_boxed_2661_, v_b_2659_);
lean_dec_ref(v_as_2656_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21___boxed(lean_object* v_x_2663_, lean_object* v_x_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(v_x_2663_, v_x_2664_);
lean_dec_ref(v_x_2663_);
return v_res_2665_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0(void){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2666_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(lean_object* v_x_2667_, size_t v_x_2668_, size_t v_x_2669_, lean_object* v_x_2670_){
_start:
{
if (lean_obj_tag(v_x_2667_) == 0)
{
lean_object* v_cs_2671_; lean_object* v___x_2672_; size_t v___x_2673_; lean_object* v_j_2674_; lean_object* v___x_2675_; size_t v___x_2676_; size_t v___x_2677_; size_t v___x_2678_; size_t v___x_2679_; size_t v___x_2680_; size_t v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
v_cs_2671_ = lean_ctor_get(v_x_2667_, 0);
v___x_2672_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0);
v___x_2673_ = lean_usize_shift_right(v_x_2668_, v_x_2669_);
v_j_2674_ = lean_usize_to_nat(v___x_2673_);
v___x_2675_ = lean_array_get_borrowed(v___x_2672_, v_cs_2671_, v_j_2674_);
v___x_2676_ = ((size_t)1ULL);
v___x_2677_ = lean_usize_shift_left(v___x_2676_, v_x_2669_);
v___x_2678_ = lean_usize_sub(v___x_2677_, v___x_2676_);
v___x_2679_ = lean_usize_land(v_x_2668_, v___x_2678_);
v___x_2680_ = ((size_t)5ULL);
v___x_2681_ = lean_usize_sub(v_x_2669_, v___x_2680_);
v___x_2682_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(v___x_2675_, v___x_2679_, v___x_2681_, v_x_2670_);
v___x_2683_ = lean_unsigned_to_nat(1u);
v___x_2684_ = lean_nat_add(v_j_2674_, v___x_2683_);
lean_dec(v_j_2674_);
v___x_2685_ = lean_array_get_size(v_cs_2671_);
v___x_2686_ = lean_nat_dec_lt(v___x_2684_, v___x_2685_);
if (v___x_2686_ == 0)
{
lean_dec(v___x_2684_);
return v___x_2682_;
}
else
{
size_t v___x_2687_; size_t v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = lean_usize_of_nat(v___x_2684_);
lean_dec(v___x_2684_);
v___x_2688_ = lean_usize_of_nat(v___x_2685_);
v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_spec__26(v_cs_2671_, v___x_2687_, v___x_2688_, v___x_2682_);
return v___x_2689_;
}
}
else
{
lean_object* v_vs_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v_vs_2690_ = lean_ctor_get(v_x_2667_, 0);
v___x_2691_ = lean_usize_to_nat(v_x_2668_);
v___x_2692_ = lean_array_get_size(v_vs_2690_);
v___x_2693_ = lean_nat_dec_lt(v___x_2691_, v___x_2692_);
if (v___x_2693_ == 0)
{
lean_dec(v___x_2691_);
return v_x_2670_;
}
else
{
size_t v___x_2694_; size_t v___x_2695_; lean_object* v___x_2696_; 
v___x_2694_ = lean_usize_of_nat(v___x_2691_);
lean_dec(v___x_2691_);
v___x_2695_ = lean_usize_of_nat(v___x_2692_);
v___x_2696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_vs_2690_, v___x_2694_, v___x_2695_, v_x_2670_);
return v___x_2696_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2667_ = stack[0].m_obj;
size_t v_x_2668_ = stack[1].m_num;
size_t v_x_2669_ = stack[2].m_num;
lean_object* v_x_2670_ = stack[3].m_obj;
lean_object* v_res_2697_;
v_res_2697_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(v_x_2667_, v_x_2668_, v_x_2669_, v_x_2670_);
stack->m_obj
 = v_res_2697_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___boxed(lean_object* v_x_2698_, lean_object* v_x_2699_, lean_object* v_x_2700_, lean_object* v_x_2701_){
_start:
{
size_t v_x_97199__boxed_2702_; size_t v_x_97200__boxed_2703_; lean_object* v_res_2704_; 
v_x_97199__boxed_2702_ = lean_unbox_usize(v_x_2699_);
lean_dec(v_x_2699_);
v_x_97200__boxed_2703_ = lean_unbox_usize(v_x_2700_);
lean_dec(v_x_2700_);
v_res_2704_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(v_x_2698_, v_x_97199__boxed_2702_, v_x_97200__boxed_2703_, v_x_2701_);
lean_dec_ref(v_x_2698_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object* v_t_2705_, lean_object* v_init_2706_, lean_object* v_start_2707_){
_start:
{
lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2708_ = lean_unsigned_to_nat(0u);
v___x_2709_ = lean_nat_dec_eq(v_start_2707_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v_root_2710_; lean_object* v_tail_2711_; size_t v_shift_2712_; lean_object* v_tailOff_2713_; uint8_t v___x_2714_; 
v_root_2710_ = lean_ctor_get(v_t_2705_, 0);
v_tail_2711_ = lean_ctor_get(v_t_2705_, 1);
v_shift_2712_ = lean_ctor_get_usize(v_t_2705_, 4);
v_tailOff_2713_ = lean_ctor_get(v_t_2705_, 3);
v___x_2714_ = lean_nat_dec_le(v_tailOff_2713_, v_start_2707_);
if (v___x_2714_ == 0)
{
size_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2715_ = lean_usize_of_nat(v_start_2707_);
v___x_2716_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19(v_root_2710_, v___x_2715_, v_shift_2712_, v_init_2706_);
v___x_2717_ = lean_array_get_size(v_tail_2711_);
v___x_2718_ = lean_nat_dec_lt(v___x_2708_, v___x_2717_);
if (v___x_2718_ == 0)
{
return v___x_2716_;
}
else
{
size_t v___x_2719_; size_t v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = ((size_t)0ULL);
v___x_2720_ = lean_usize_of_nat(v___x_2717_);
v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_tail_2711_, v___x_2719_, v___x_2720_, v___x_2716_);
return v___x_2721_;
}
}
else
{
lean_object* v___x_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2722_ = lean_nat_sub(v_start_2707_, v_tailOff_2713_);
v___x_2723_ = lean_array_get_size(v_tail_2711_);
v___x_2724_ = lean_nat_dec_lt(v___x_2722_, v___x_2723_);
if (v___x_2724_ == 0)
{
lean_dec(v___x_2722_);
return v_init_2706_;
}
else
{
size_t v___x_2725_; size_t v___x_2726_; lean_object* v___x_2727_; 
v___x_2725_ = lean_usize_of_nat(v___x_2722_);
lean_dec(v___x_2722_);
v___x_2726_ = lean_usize_of_nat(v___x_2723_);
v___x_2727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_tail_2711_, v___x_2725_, v___x_2726_, v_init_2706_);
return v___x_2727_;
}
}
}
else
{
lean_object* v_root_2728_; lean_object* v_tail_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v_root_2728_ = lean_ctor_get(v_t_2705_, 0);
v_tail_2729_ = lean_ctor_get(v_t_2705_, 1);
v___x_2730_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__21(v_root_2728_, v_init_2706_);
v___x_2731_ = lean_array_get_size(v_tail_2729_);
v___x_2732_ = lean_nat_dec_lt(v___x_2708_, v___x_2731_);
if (v___x_2732_ == 0)
{
return v___x_2730_;
}
else
{
size_t v___x_2733_; size_t v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = ((size_t)0ULL);
v___x_2734_ = lean_usize_of_nat(v___x_2731_);
v___x_2735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__20(v_tail_2729_, v___x_2733_, v___x_2734_, v___x_2730_);
return v___x_2735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(lean_object* v_t_2736_, lean_object* v_init_2737_, lean_object* v_start_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_t_2736_, v_init_2737_, v_start_2738_);
lean_dec(v_start_2738_);
lean_dec_ref(v_t_2736_);
return v_res_2739_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object* v___x_2740_, size_t v_sz_2741_, size_t v_i_2742_, lean_object* v_bs_2743_){
_start:
{
uint8_t v___x_2744_; 
v___x_2744_ = lean_usize_dec_lt(v_i_2742_, v_sz_2741_);
if (v___x_2744_ == 0)
{
return v_bs_2743_;
}
else
{
lean_object* v_v_2745_; lean_object* v___x_2746_; lean_object* v_bs_x27_2747_; lean_object* v___x_2748_; size_t v___x_2749_; size_t v___x_2750_; lean_object* v___x_2751_; 
v_v_2745_ = lean_array_uget(v_bs_2743_, v_i_2742_);
v___x_2746_ = lean_unsigned_to_nat(0u);
v_bs_x27_2747_ = lean_array_uset(v_bs_2743_, v_i_2742_, v___x_2746_);
v___x_2748_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_v_2745_, v___x_2740_);
v___x_2749_ = ((size_t)1ULL);
v___x_2750_ = lean_usize_add(v_i_2742_, v___x_2749_);
v___x_2751_ = lean_array_uset(v_bs_x27_2747_, v_i_2742_, v___x_2748_);
v_i_2742_ = v___x_2750_;
v_bs_2743_ = v___x_2751_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2740_ = stack[0].m_obj;
size_t v_sz_2741_ = stack[1].m_num;
size_t v_i_2742_ = stack[2].m_num;
lean_object* v_bs_2743_ = stack[3].m_obj;
lean_object* v_res_2753_;
v_res_2753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v___x_2740_, v_sz_2741_, v_i_2742_, v_bs_2743_);
stack->m_obj
 = v_res_2753_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9___boxed(lean_object* v___x_2754_, lean_object* v_sz_2755_, lean_object* v_i_2756_, lean_object* v_bs_2757_){
_start:
{
size_t v_sz_boxed_2758_; size_t v_i_boxed_2759_; lean_object* v_res_2760_; 
v_sz_boxed_2758_ = lean_unbox_usize(v_sz_2755_);
lean_dec(v_sz_2755_);
v_i_boxed_2759_ = lean_unbox_usize(v_i_2756_);
lean_dec(v_i_2756_);
v_res_2760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v___x_2754_, v_sz_boxed_2758_, v_i_boxed_2759_, v_bs_2757_);
lean_dec_ref(v___x_2754_);
return v_res_2760_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object* v_as_2761_, size_t v_sz_2762_, size_t v_i_2763_, lean_object* v_b_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_usize_dec_lt(v_i_2763_, v_sz_2762_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v_b_2764_);
return v___x_2777_;
}
else
{
lean_object* v___x_2778_; lean_object* v_a_2779_; lean_object* v___x_2780_; 
v___x_2778_ = lean_box(0);
v_a_2779_ = lean_array_uget_borrowed(v_as_2761_, v_i_2763_);
lean_inc_ref(v___y_2773_);
lean_inc(v_a_2779_);
v___x_2780_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_a_2779_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
if (lean_obj_tag(v___x_2780_) == 0)
{
size_t v___x_2781_; size_t v___x_2782_; 
lean_dec_ref_known(v___x_2780_, 1);
v___x_2781_ = ((size_t)1ULL);
v___x_2782_ = lean_usize_add(v_i_2763_, v___x_2781_);
v_i_2763_ = v___x_2782_;
v_b_2764_ = v___x_2778_;
goto _start;
}
else
{
return v___x_2780_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2761_ = stack[0].m_obj;
size_t v_sz_2762_ = stack[1].m_num;
size_t v_i_2763_ = stack[2].m_num;
lean_object* v_b_2764_ = stack[3].m_obj;
lean_object* v___y_2765_ = stack[4].m_obj;
lean_object* v___y_2766_ = stack[5].m_obj;
lean_object* v___y_2767_ = stack[6].m_obj;
lean_object* v___y_2768_ = stack[7].m_obj;
lean_object* v___y_2769_ = stack[8].m_obj;
lean_object* v___y_2770_ = stack[9].m_obj;
lean_object* v___y_2771_ = stack[10].m_obj;
lean_object* v___y_2772_ = stack[11].m_obj;
lean_object* v___y_2773_ = stack[12].m_obj;
lean_object* v___y_2774_ = stack[13].m_obj;
lean_object* v_res_2784_;
v_res_2784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v_as_2761_, v_sz_2762_, v_i_2763_, v_b_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
stack->m_obj
 = v_res_2784_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object* v_as_2785_, lean_object* v_sz_2786_, lean_object* v_i_2787_, lean_object* v_b_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
size_t v_sz_boxed_2800_; size_t v_i_boxed_2801_; lean_object* v_res_2802_; 
v_sz_boxed_2800_ = lean_unbox_usize(v_sz_2786_);
lean_dec(v_sz_2786_);
v_i_boxed_2801_ = lean_unbox_usize(v_i_2787_);
lean_dec(v_i_2787_);
v_res_2802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v_as_2785_, v_sz_boxed_2800_, v_i_boxed_2801_, v_b_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v_as_2785_);
return v_res_2802_;
}
}
uint8_t l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(uint8_t v___x_2803_, lean_object* v_a_2804_, lean_object* v___x_2805_, uint8_t v___x_2806_, lean_object* v_x_2807_){
_start:
{
if (lean_obj_tag(v_x_2807_) == 0)
{
uint8_t v___x_2808_; 
v___x_2808_ = 0;
return v___x_2808_;
}
else
{
lean_object* v_head_2809_; lean_object* v_tail_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v_head_2809_ = lean_ctor_get(v_x_2807_, 0);
v_tail_2810_ = lean_ctor_get(v_x_2807_, 1);
v___x_2811_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_2812_ = 1;
v___x_2819_ = lean_unsigned_to_nat(0u);
v___x_2820_ = lean_array_get_borrowed(v___x_2819_, v___x_2805_, v_head_2809_);
v___x_2821_ = lean_nat_dec_eq(v___x_2820_, v_head_2809_);
if (v___x_2821_ == 0)
{
goto v___jp_2813_;
}
else
{
if (v___x_2806_ == 0)
{
v_x_2807_ = v_tail_2810_;
goto _start;
}
else
{
goto v___jp_2813_;
}
}
v___jp_2813_:
{
if (v___x_2803_ == 0)
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2814_ = lean_unsigned_to_nat(1u);
v___x_2815_ = lean_array_get_borrowed(v___x_2811_, v_a_2804_, v_head_2809_);
v___x_2816_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_2815_);
v___x_2817_ = lean_nat_dec_lt(v___x_2814_, v___x_2816_);
lean_dec(v___x_2816_);
if (v___x_2817_ == 0)
{
v_x_2807_ = v_tail_2810_;
goto _start;
}
else
{
return v___x_2817_;
}
}
else
{
return v___x_2812_;
}
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2803_ = stack[0].m_num;
lean_object* v_a_2804_ = stack[1].m_obj;
lean_object* v___x_2805_ = stack[2].m_obj;
uint8_t v___x_2806_ = stack[3].m_num;
lean_object* v_x_2807_ = stack[4].m_obj;
uint8_t v_res_2823_;
v_res_2823_ = l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(v___x_2803_, v_a_2804_, v___x_2805_, v___x_2806_, v_x_2807_);
stack->m_num = v_res_2823_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___boxed(lean_object* v___x_2824_, lean_object* v_a_2825_, lean_object* v___x_2826_, lean_object* v___x_2827_, lean_object* v_x_2828_){
_start:
{
uint8_t v___x_97465__boxed_2829_; uint8_t v___x_97468__boxed_2830_; uint8_t v_res_2831_; lean_object* v_r_2832_; 
v___x_97465__boxed_2829_ = lean_unbox(v___x_2824_);
v___x_97468__boxed_2830_ = lean_unbox(v___x_2827_);
v_res_2831_ = l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(v___x_97465__boxed_2829_, v_a_2825_, v___x_2826_, v___x_97468__boxed_2830_, v_x_2828_);
lean_dec(v_x_2828_);
lean_dec_ref(v___x_2826_);
lean_dec_ref(v_a_2825_);
v_r_2832_ = lean_box(v_res_2831_);
return v_r_2832_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(lean_object* v_as_2833_, size_t v_i_2834_, size_t v_stop_2835_, lean_object* v_b_2836_){
_start:
{
uint8_t v___x_2837_; 
v___x_2837_ = lean_usize_dec_eq(v_i_2834_, v_stop_2835_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; size_t v___x_2841_; size_t v___x_2842_; 
v___x_2838_ = lean_array_uget_borrowed(v_as_2833_, v_i_2834_);
v___x_2839_ = l_Lean_PersistentArray_toArray___redArg(v___x_2838_);
v___x_2840_ = l_Array_append___redArg(v_b_2836_, v___x_2839_);
lean_dec_ref(v___x_2839_);
v___x_2841_ = ((size_t)1ULL);
v___x_2842_ = lean_usize_add(v_i_2834_, v___x_2841_);
v_i_2834_ = v___x_2842_;
v_b_2836_ = v___x_2840_;
goto _start;
}
else
{
return v_b_2836_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2833_ = stack[0].m_obj;
size_t v_i_2834_ = stack[1].m_num;
size_t v_stop_2835_ = stack[2].m_num;
lean_object* v_b_2836_ = stack[3].m_obj;
lean_object* v_res_2844_;
v_res_2844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_as_2833_, v_i_2834_, v_stop_2835_, v_b_2836_);
stack->m_obj
 = v_res_2844_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25___boxed(lean_object* v_as_2845_, lean_object* v_i_2846_, lean_object* v_stop_2847_, lean_object* v_b_2848_){
_start:
{
size_t v_i_boxed_2849_; size_t v_stop_boxed_2850_; lean_object* v_res_2851_; 
v_i_boxed_2849_ = lean_unbox_usize(v_i_2846_);
lean_dec(v_i_2846_);
v_stop_boxed_2850_ = lean_unbox_usize(v_stop_2847_);
lean_dec(v_stop_2847_);
v_res_2851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_as_2845_, v_i_boxed_2849_, v_stop_boxed_2850_, v_b_2848_);
lean_dec_ref(v_as_2845_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(lean_object* v_x_2852_, lean_object* v_x_2853_){
_start:
{
if (lean_obj_tag(v_x_2852_) == 0)
{
lean_object* v_cs_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; 
v_cs_2854_ = lean_ctor_get(v_x_2852_, 0);
v___x_2855_ = lean_unsigned_to_nat(0u);
v___x_2856_ = lean_array_get_size(v_cs_2854_);
v___x_2857_ = lean_nat_dec_lt(v___x_2855_, v___x_2856_);
if (v___x_2857_ == 0)
{
return v_x_2853_;
}
else
{
size_t v___x_2858_; size_t v___x_2859_; lean_object* v___x_2860_; 
v___x_2858_ = ((size_t)0ULL);
v___x_2859_ = lean_usize_of_nat(v___x_2856_);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(v_cs_2854_, v___x_2858_, v___x_2859_, v_x_2853_);
return v___x_2860_;
}
}
else
{
lean_object* v_vs_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v_vs_2861_ = lean_ctor_get(v_x_2852_, 0);
v___x_2862_ = lean_unsigned_to_nat(0u);
v___x_2863_ = lean_array_get_size(v_vs_2861_);
v___x_2864_ = lean_nat_dec_lt(v___x_2862_, v___x_2863_);
if (v___x_2864_ == 0)
{
return v_x_2853_;
}
else
{
size_t v___x_2865_; size_t v___x_2866_; lean_object* v___x_2867_; 
v___x_2865_ = ((size_t)0ULL);
v___x_2866_ = lean_usize_of_nat(v___x_2863_);
v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_vs_2861_, v___x_2865_, v___x_2866_, v_x_2853_);
return v___x_2867_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(lean_object* v_as_2868_, size_t v_i_2869_, size_t v_stop_2870_, lean_object* v_b_2871_){
_start:
{
uint8_t v___x_2872_; 
v___x_2872_ = lean_usize_dec_eq(v_i_2869_, v_stop_2870_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; lean_object* v___x_2874_; size_t v___x_2875_; size_t v___x_2876_; 
v___x_2873_ = lean_array_uget_borrowed(v_as_2868_, v_i_2869_);
v___x_2874_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(v___x_2873_, v_b_2871_);
v___x_2875_ = ((size_t)1ULL);
v___x_2876_ = lean_usize_add(v_i_2869_, v___x_2875_);
v_i_2869_ = v___x_2876_;
v_b_2871_ = v___x_2874_;
goto _start;
}
else
{
return v_b_2871_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2868_ = stack[0].m_obj;
size_t v_i_2869_ = stack[1].m_num;
size_t v_stop_2870_ = stack[2].m_num;
lean_object* v_b_2871_ = stack[3].m_obj;
lean_object* v_res_2878_;
v_res_2878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(v_as_2868_, v_i_2869_, v_stop_2870_, v_b_2871_);
stack->m_obj
 = v_res_2878_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32___boxed(lean_object* v_as_2879_, lean_object* v_i_2880_, lean_object* v_stop_2881_, lean_object* v_b_2882_){
_start:
{
size_t v_i_boxed_2883_; size_t v_stop_boxed_2884_; lean_object* v_res_2885_; 
v_i_boxed_2883_ = lean_unbox_usize(v_i_2880_);
lean_dec(v_i_2880_);
v_stop_boxed_2884_ = lean_unbox_usize(v_stop_2881_);
lean_dec(v_stop_2881_);
v_res_2885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(v_as_2879_, v_i_boxed_2883_, v_stop_boxed_2884_, v_b_2882_);
lean_dec_ref(v_as_2879_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26___boxed(lean_object* v_x_2886_, lean_object* v_x_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(v_x_2886_, v_x_2887_);
lean_dec_ref(v_x_2886_);
return v_res_2888_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(lean_object* v_x_2889_, size_t v_x_2890_, size_t v_x_2891_, lean_object* v_x_2892_){
_start:
{
if (lean_obj_tag(v_x_2889_) == 0)
{
lean_object* v_cs_2893_; lean_object* v___x_2894_; size_t v___x_2895_; lean_object* v_j_2896_; lean_object* v___x_2897_; size_t v___x_2898_; size_t v___x_2899_; size_t v___x_2900_; size_t v___x_2901_; size_t v___x_2902_; size_t v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v_cs_2893_ = lean_ctor_get(v_x_2889_, 0);
v___x_2894_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0);
v___x_2895_ = lean_usize_shift_right(v_x_2890_, v_x_2891_);
v_j_2896_ = lean_usize_to_nat(v___x_2895_);
v___x_2897_ = lean_array_get_borrowed(v___x_2894_, v_cs_2893_, v_j_2896_);
v___x_2898_ = ((size_t)1ULL);
v___x_2899_ = lean_usize_shift_left(v___x_2898_, v_x_2891_);
v___x_2900_ = lean_usize_sub(v___x_2899_, v___x_2898_);
v___x_2901_ = lean_usize_land(v_x_2890_, v___x_2900_);
v___x_2902_ = ((size_t)5ULL);
v___x_2903_ = lean_usize_sub(v_x_2891_, v___x_2902_);
v___x_2904_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(v___x_2897_, v___x_2901_, v___x_2903_, v_x_2892_);
v___x_2905_ = lean_unsigned_to_nat(1u);
v___x_2906_ = lean_nat_add(v_j_2896_, v___x_2905_);
lean_dec(v_j_2896_);
v___x_2907_ = lean_array_get_size(v_cs_2893_);
v___x_2908_ = lean_nat_dec_lt(v___x_2906_, v___x_2907_);
if (v___x_2908_ == 0)
{
lean_dec(v___x_2906_);
return v___x_2904_;
}
else
{
size_t v___x_2909_; size_t v___x_2910_; lean_object* v___x_2911_; 
v___x_2909_ = lean_usize_of_nat(v___x_2906_);
lean_dec(v___x_2906_);
v___x_2910_ = lean_usize_of_nat(v___x_2907_);
v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_spec__32(v_cs_2893_, v___x_2909_, v___x_2910_, v___x_2904_);
return v___x_2911_;
}
}
else
{
lean_object* v_vs_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v_vs_2912_ = lean_ctor_get(v_x_2889_, 0);
v___x_2913_ = lean_usize_to_nat(v_x_2890_);
v___x_2914_ = lean_array_get_size(v_vs_2912_);
v___x_2915_ = lean_nat_dec_lt(v___x_2913_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_dec(v___x_2913_);
return v_x_2892_;
}
else
{
size_t v___x_2916_; size_t v___x_2917_; lean_object* v___x_2918_; 
v___x_2916_ = lean_usize_of_nat(v___x_2913_);
lean_dec(v___x_2913_);
v___x_2917_ = lean_usize_of_nat(v___x_2914_);
v___x_2918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_vs_2912_, v___x_2916_, v___x_2917_, v_x_2892_);
return v___x_2918_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2889_ = stack[0].m_obj;
size_t v_x_2890_ = stack[1].m_num;
size_t v_x_2891_ = stack[2].m_num;
lean_object* v_x_2892_ = stack[3].m_obj;
lean_object* v_res_2919_;
v_res_2919_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(v_x_2889_, v_x_2890_, v_x_2891_, v_x_2892_);
stack->m_obj
 = v_res_2919_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24___boxed(lean_object* v_x_2920_, lean_object* v_x_2921_, lean_object* v_x_2922_, lean_object* v_x_2923_){
_start:
{
size_t v_x_97628__boxed_2924_; size_t v_x_97629__boxed_2925_; lean_object* v_res_2926_; 
v_x_97628__boxed_2924_ = lean_unbox_usize(v_x_2921_);
lean_dec(v_x_2921_);
v_x_97629__boxed_2925_ = lean_unbox_usize(v_x_2922_);
lean_dec(v_x_2922_);
v_res_2926_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(v_x_2920_, v_x_97628__boxed_2924_, v_x_97629__boxed_2925_, v_x_2923_);
lean_dec_ref(v_x_2920_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object* v_t_2927_, lean_object* v_init_2928_, lean_object* v_start_2929_){
_start:
{
lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2930_ = lean_unsigned_to_nat(0u);
v___x_2931_ = lean_nat_dec_eq(v_start_2929_, v___x_2930_);
if (v___x_2931_ == 0)
{
lean_object* v_root_2932_; lean_object* v_tail_2933_; size_t v_shift_2934_; lean_object* v_tailOff_2935_; uint8_t v___x_2936_; 
v_root_2932_ = lean_ctor_get(v_t_2927_, 0);
v_tail_2933_ = lean_ctor_get(v_t_2927_, 1);
v_shift_2934_ = lean_ctor_get_usize(v_t_2927_, 4);
v_tailOff_2935_ = lean_ctor_get(v_t_2927_, 3);
v___x_2936_ = lean_nat_dec_le(v_tailOff_2935_, v_start_2929_);
if (v___x_2936_ == 0)
{
size_t v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v___x_2937_ = lean_usize_of_nat(v_start_2929_);
v___x_2938_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__24(v_root_2932_, v___x_2937_, v_shift_2934_, v_init_2928_);
v___x_2939_ = lean_array_get_size(v_tail_2933_);
v___x_2940_ = lean_nat_dec_lt(v___x_2930_, v___x_2939_);
if (v___x_2940_ == 0)
{
return v___x_2938_;
}
else
{
size_t v___x_2941_; size_t v___x_2942_; lean_object* v___x_2943_; 
v___x_2941_ = ((size_t)0ULL);
v___x_2942_ = lean_usize_of_nat(v___x_2939_);
v___x_2943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_tail_2933_, v___x_2941_, v___x_2942_, v___x_2938_);
return v___x_2943_;
}
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v___x_2944_ = lean_nat_sub(v_start_2929_, v_tailOff_2935_);
v___x_2945_ = lean_array_get_size(v_tail_2933_);
v___x_2946_ = lean_nat_dec_lt(v___x_2944_, v___x_2945_);
if (v___x_2946_ == 0)
{
lean_dec(v___x_2944_);
return v_init_2928_;
}
else
{
size_t v___x_2947_; size_t v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = lean_usize_of_nat(v___x_2944_);
lean_dec(v___x_2944_);
v___x_2948_ = lean_usize_of_nat(v___x_2945_);
v___x_2949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_tail_2933_, v___x_2947_, v___x_2948_, v_init_2928_);
return v___x_2949_;
}
}
}
else
{
lean_object* v_root_2950_; lean_object* v_tail_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v_root_2950_ = lean_ctor_get(v_t_2927_, 0);
v_tail_2951_ = lean_ctor_get(v_t_2927_, 1);
v___x_2952_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__26(v_root_2950_, v_init_2928_);
v___x_2953_ = lean_array_get_size(v_tail_2951_);
v___x_2954_ = lean_nat_dec_lt(v___x_2930_, v___x_2953_);
if (v___x_2954_ == 0)
{
return v___x_2952_;
}
else
{
size_t v___x_2955_; size_t v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = ((size_t)0ULL);
v___x_2956_ = lean_usize_of_nat(v___x_2953_);
v___x_2957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10_spec__25(v_tail_2951_, v___x_2955_, v___x_2956_, v___x_2952_);
return v___x_2957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(lean_object* v_t_2958_, lean_object* v_init_2959_, lean_object* v_start_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v_t_2958_, v_init_2959_, v_start_2960_);
lean_dec(v_start_2960_);
lean_dec_ref(v_t_2958_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
if (lean_obj_tag(v_a_2962_) == 0)
{
lean_object* v___x_2964_; 
v___x_2964_ = l_List_reverse___redArg(v_a_2963_);
return v___x_2964_;
}
else
{
lean_object* v_head_2965_; lean_object* v_tail_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2977_; 
v_head_2965_ = lean_ctor_get(v_a_2962_, 0);
v_tail_2966_ = lean_ctor_get(v_a_2962_, 1);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_a_2962_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2968_ = v_a_2962_;
v_isShared_2969_ = v_isSharedCheck_2977_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_tail_2966_);
lean_inc(v_head_2965_);
lean_dec(v_a_2962_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2977_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2970_ = l_Nat_reprFast(v_head_2965_);
v___x_2971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
v___x_2972_ = l_Lean_MessageData_ofFormat(v___x_2971_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 1, v_a_2963_);
lean_ctor_set(v___x_2968_, 0, v___x_2972_);
v___x_2974_ = v___x_2968_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_a_2963_);
v___x_2974_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
v_a_2962_ = v_tail_2966_;
v_a_2963_ = v___x_2974_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object* v___x_2978_, size_t v_sz_2979_, size_t v_i_2980_, lean_object* v_bs_2981_){
_start:
{
uint8_t v___x_2982_; 
v___x_2982_ = lean_usize_dec_lt(v_i_2980_, v_sz_2979_);
if (v___x_2982_ == 0)
{
return v_bs_2981_;
}
else
{
lean_object* v_v_2983_; lean_object* v___x_2984_; lean_object* v_bs_x27_2985_; lean_object* v___x_2986_; size_t v___x_2987_; size_t v___x_2988_; lean_object* v___x_2989_; 
v_v_2983_ = lean_array_uget(v_bs_2981_, v_i_2980_);
v___x_2984_ = lean_unsigned_to_nat(0u);
v_bs_x27_2985_ = lean_array_uset(v_bs_2981_, v_i_2980_, v___x_2984_);
v___x_2986_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_v_2983_, v___x_2978_);
v___x_2987_ = ((size_t)1ULL);
v___x_2988_ = lean_usize_add(v_i_2980_, v___x_2987_);
v___x_2989_ = lean_array_uset(v_bs_x27_2985_, v_i_2980_, v___x_2986_);
v_i_2980_ = v___x_2988_;
v_bs_2981_ = v___x_2989_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2978_ = stack[0].m_obj;
size_t v_sz_2979_ = stack[1].m_num;
size_t v_i_2980_ = stack[2].m_num;
lean_object* v_bs_2981_ = stack[3].m_obj;
lean_object* v_res_2991_;
v_res_2991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v___x_2978_, v_sz_2979_, v_i_2980_, v_bs_2981_);
stack->m_obj
 = v_res_2991_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(lean_object* v___x_2992_, lean_object* v_sz_2993_, lean_object* v_i_2994_, lean_object* v_bs_2995_){
_start:
{
size_t v_sz_boxed_2996_; size_t v_i_boxed_2997_; lean_object* v_res_2998_; 
v_sz_boxed_2996_ = lean_unbox_usize(v_sz_2993_);
lean_dec(v_sz_2993_);
v_i_boxed_2997_ = lean_unbox_usize(v_i_2994_);
lean_dec(v_i_2994_);
v_res_2998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v___x_2992_, v_sz_boxed_2996_, v_i_boxed_2997_, v_bs_2995_);
lean_dec_ref(v___x_2992_);
return v_res_2998_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object* v_as_2999_, size_t v_sz_3000_, size_t v_i_3001_, lean_object* v_b_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
uint8_t v___x_3014_; 
v___x_3014_ = lean_usize_dec_lt(v_i_3001_, v_sz_3000_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_b_3002_);
return v___x_3015_;
}
else
{
lean_object* v___x_3016_; lean_object* v_a_3017_; lean_object* v___x_3018_; 
v___x_3016_ = lean_box(0);
v_a_3017_ = lean_array_uget_borrowed(v_as_2999_, v_i_3001_);
lean_inc(v_a_3017_);
v___x_3018_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(v_a_3017_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
if (lean_obj_tag(v___x_3018_) == 0)
{
size_t v___x_3019_; size_t v___x_3020_; 
lean_dec_ref_known(v___x_3018_, 1);
v___x_3019_ = ((size_t)1ULL);
v___x_3020_ = lean_usize_add(v_i_3001_, v___x_3019_);
v_i_3001_ = v___x_3020_;
v_b_3002_ = v___x_3016_;
goto _start;
}
else
{
return v___x_3018_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2999_ = stack[0].m_obj;
size_t v_sz_3000_ = stack[1].m_num;
size_t v_i_3001_ = stack[2].m_num;
lean_object* v_b_3002_ = stack[3].m_obj;
lean_object* v___y_3003_ = stack[4].m_obj;
lean_object* v___y_3004_ = stack[5].m_obj;
lean_object* v___y_3005_ = stack[6].m_obj;
lean_object* v___y_3006_ = stack[7].m_obj;
lean_object* v___y_3007_ = stack[8].m_obj;
lean_object* v___y_3008_ = stack[9].m_obj;
lean_object* v___y_3009_ = stack[10].m_obj;
lean_object* v___y_3010_ = stack[11].m_obj;
lean_object* v___y_3011_ = stack[12].m_obj;
lean_object* v___y_3012_ = stack[13].m_obj;
lean_object* v_res_3022_;
v_res_3022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v_as_2999_, v_sz_3000_, v_i_3001_, v_b_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
stack->m_obj
 = v_res_3022_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16___boxed(lean_object* v_as_3023_, lean_object* v_sz_3024_, lean_object* v_i_3025_, lean_object* v_b_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
size_t v_sz_boxed_3038_; size_t v_i_boxed_3039_; lean_object* v_res_3040_; 
v_sz_boxed_3038_ = lean_unbox_usize(v_sz_3024_);
lean_dec(v_sz_3024_);
v_i_boxed_3039_ = lean_unbox_usize(v_i_3025_);
lean_dec(v_i_3025_);
v_res_3040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v_as_3023_, v_sz_boxed_3038_, v_i_boxed_3039_, v_b_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v_as_3023_);
return v_res_3040_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object* v_as_3041_, size_t v_sz_3042_, size_t v_i_3043_, lean_object* v_b_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
uint8_t v___x_3056_; 
v___x_3056_ = lean_usize_dec_lt(v_i_3043_, v_sz_3042_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v_b_3044_);
return v___x_3057_;
}
else
{
lean_object* v___x_3058_; lean_object* v_a_3059_; lean_object* v___x_3060_; 
v___x_3058_ = lean_box(0);
v_a_3059_ = lean_array_uget_borrowed(v_as_3041_, v_i_3043_);
lean_inc(v___y_3054_);
lean_inc_ref(v___y_3053_);
lean_inc(v___y_3052_);
lean_inc_ref(v___y_3051_);
lean_inc(v___y_3050_);
lean_inc_ref(v___y_3049_);
lean_inc(v___y_3048_);
lean_inc_ref(v___y_3047_);
lean_inc(v___y_3046_);
lean_inc(v___y_3045_);
lean_inc(v_a_3059_);
v___x_3060_ = lean_grind_cutsat_assert_le(v_a_3059_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
if (lean_obj_tag(v___x_3060_) == 0)
{
size_t v___x_3061_; size_t v___x_3062_; 
lean_dec_ref_known(v___x_3060_, 1);
v___x_3061_ = ((size_t)1ULL);
v___x_3062_ = lean_usize_add(v_i_3043_, v___x_3061_);
v_i_3043_ = v___x_3062_;
v_b_3044_ = v___x_3058_;
goto _start;
}
else
{
return v___x_3060_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3041_ = stack[0].m_obj;
size_t v_sz_3042_ = stack[1].m_num;
size_t v_i_3043_ = stack[2].m_num;
lean_object* v_b_3044_ = stack[3].m_obj;
lean_object* v___y_3045_ = stack[4].m_obj;
lean_object* v___y_3046_ = stack[5].m_obj;
lean_object* v___y_3047_ = stack[6].m_obj;
lean_object* v___y_3048_ = stack[7].m_obj;
lean_object* v___y_3049_ = stack[8].m_obj;
lean_object* v___y_3050_ = stack[9].m_obj;
lean_object* v___y_3051_ = stack[10].m_obj;
lean_object* v___y_3052_ = stack[11].m_obj;
lean_object* v___y_3053_ = stack[12].m_obj;
lean_object* v___y_3054_ = stack[13].m_obj;
lean_object* v_res_3064_;
v_res_3064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v_as_3041_, v_sz_3042_, v_i_3043_, v_b_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
stack->m_obj
 = v_res_3064_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object* v_as_3065_, lean_object* v_sz_3066_, lean_object* v_i_3067_, lean_object* v_b_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
size_t v_sz_boxed_3080_; size_t v_i_boxed_3081_; lean_object* v_res_3082_; 
v_sz_boxed_3080_ = lean_unbox_usize(v_sz_3066_);
lean_dec(v_sz_3066_);
v_i_boxed_3081_ = lean_unbox_usize(v_i_3067_);
lean_dec(v_i_3067_);
v_res_3082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v_as_3065_, v_sz_boxed_3080_, v_i_boxed_3081_, v_b_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v_as_3065_);
return v_res_3082_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(lean_object* v_as_3083_, size_t v_i_3084_, size_t v_stop_3085_, lean_object* v_b_3086_){
_start:
{
uint8_t v___x_3087_; 
v___x_3087_ = lean_usize_dec_eq(v_i_3084_, v_stop_3085_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; size_t v___x_3091_; size_t v___x_3092_; 
v___x_3088_ = lean_array_uget_borrowed(v_as_3083_, v_i_3084_);
v___x_3089_ = l_Lean_PersistentArray_toArray___redArg(v___x_3088_);
v___x_3090_ = l_Array_append___redArg(v_b_3086_, v___x_3089_);
lean_dec_ref(v___x_3089_);
v___x_3091_ = ((size_t)1ULL);
v___x_3092_ = lean_usize_add(v_i_3084_, v___x_3091_);
v_i_3084_ = v___x_3092_;
v_b_3086_ = v___x_3090_;
goto _start;
}
else
{
return v_b_3086_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3083_ = stack[0].m_obj;
size_t v_i_3084_ = stack[1].m_num;
size_t v_stop_3085_ = stack[2].m_num;
lean_object* v_b_3086_ = stack[3].m_obj;
lean_object* v_res_3094_;
v_res_3094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_as_3083_, v_i_3084_, v_stop_3085_, v_b_3086_);
stack->m_obj
 = v_res_3094_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30___boxed(lean_object* v_as_3095_, lean_object* v_i_3096_, lean_object* v_stop_3097_, lean_object* v_b_3098_){
_start:
{
size_t v_i_boxed_3099_; size_t v_stop_boxed_3100_; lean_object* v_res_3101_; 
v_i_boxed_3099_ = lean_unbox_usize(v_i_3096_);
lean_dec(v_i_3096_);
v_stop_boxed_3100_ = lean_unbox_usize(v_stop_3097_);
lean_dec(v_stop_3097_);
v_res_3101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_as_3095_, v_i_boxed_3099_, v_stop_boxed_3100_, v_b_3098_);
lean_dec_ref(v_as_3095_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(lean_object* v_x_3102_, lean_object* v_x_3103_){
_start:
{
if (lean_obj_tag(v_x_3102_) == 0)
{
lean_object* v_cs_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; uint8_t v___x_3107_; 
v_cs_3104_ = lean_ctor_get(v_x_3102_, 0);
v___x_3105_ = lean_unsigned_to_nat(0u);
v___x_3106_ = lean_array_get_size(v_cs_3104_);
v___x_3107_ = lean_nat_dec_lt(v___x_3105_, v___x_3106_);
if (v___x_3107_ == 0)
{
return v_x_3103_;
}
else
{
size_t v___x_3108_; size_t v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = ((size_t)0ULL);
v___x_3109_ = lean_usize_of_nat(v___x_3106_);
v___x_3110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(v_cs_3104_, v___x_3108_, v___x_3109_, v_x_3103_);
return v___x_3110_;
}
}
else
{
lean_object* v_vs_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v_vs_3111_ = lean_ctor_get(v_x_3102_, 0);
v___x_3112_ = lean_unsigned_to_nat(0u);
v___x_3113_ = lean_array_get_size(v_vs_3111_);
v___x_3114_ = lean_nat_dec_lt(v___x_3112_, v___x_3113_);
if (v___x_3114_ == 0)
{
return v_x_3103_;
}
else
{
size_t v___x_3115_; size_t v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = ((size_t)0ULL);
v___x_3116_ = lean_usize_of_nat(v___x_3113_);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_vs_3111_, v___x_3115_, v___x_3116_, v_x_3103_);
return v___x_3117_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(lean_object* v_as_3118_, size_t v_i_3119_, size_t v_stop_3120_, lean_object* v_b_3121_){
_start:
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_usize_dec_eq(v_i_3119_, v_stop_3120_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; lean_object* v___x_3124_; size_t v___x_3125_; size_t v___x_3126_; 
v___x_3123_ = lean_array_uget_borrowed(v_as_3118_, v_i_3119_);
v___x_3124_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(v___x_3123_, v_b_3121_);
v___x_3125_ = ((size_t)1ULL);
v___x_3126_ = lean_usize_add(v_i_3119_, v___x_3125_);
v_i_3119_ = v___x_3126_;
v_b_3121_ = v___x_3124_;
goto _start;
}
else
{
return v_b_3121_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3118_ = stack[0].m_obj;
size_t v_i_3119_ = stack[1].m_num;
size_t v_stop_3120_ = stack[2].m_num;
lean_object* v_b_3121_ = stack[3].m_obj;
lean_object* v_res_3128_;
v_res_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(v_as_3118_, v_i_3119_, v_stop_3120_, v_b_3121_);
stack->m_obj
 = v_res_3128_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38___boxed(lean_object* v_as_3129_, lean_object* v_i_3130_, lean_object* v_stop_3131_, lean_object* v_b_3132_){
_start:
{
size_t v_i_boxed_3133_; size_t v_stop_boxed_3134_; lean_object* v_res_3135_; 
v_i_boxed_3133_ = lean_unbox_usize(v_i_3130_);
lean_dec(v_i_3130_);
v_stop_boxed_3134_ = lean_unbox_usize(v_stop_3131_);
lean_dec(v_stop_3131_);
v_res_3135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(v_as_3129_, v_i_boxed_3133_, v_stop_boxed_3134_, v_b_3132_);
lean_dec_ref(v_as_3129_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31___boxed(lean_object* v_x_3136_, lean_object* v_x_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(v_x_3136_, v_x_3137_);
lean_dec_ref(v_x_3136_);
return v_res_3138_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(lean_object* v_x_3139_, size_t v_x_3140_, size_t v_x_3141_, lean_object* v_x_3142_){
_start:
{
if (lean_obj_tag(v_x_3139_) == 0)
{
lean_object* v_cs_3143_; lean_object* v___x_3144_; size_t v___x_3145_; lean_object* v_j_3146_; lean_object* v___x_3147_; size_t v___x_3148_; size_t v___x_3149_; size_t v___x_3150_; size_t v___x_3151_; size_t v___x_3152_; size_t v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; uint8_t v___x_3158_; 
v_cs_3143_ = lean_ctor_get(v_x_3139_, 0);
v___x_3144_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__19___closed__0);
v___x_3145_ = lean_usize_shift_right(v_x_3140_, v_x_3141_);
v_j_3146_ = lean_usize_to_nat(v___x_3145_);
v___x_3147_ = lean_array_get_borrowed(v___x_3144_, v_cs_3143_, v_j_3146_);
v___x_3148_ = ((size_t)1ULL);
v___x_3149_ = lean_usize_shift_left(v___x_3148_, v_x_3141_);
v___x_3150_ = lean_usize_sub(v___x_3149_, v___x_3148_);
v___x_3151_ = lean_usize_land(v_x_3140_, v___x_3150_);
v___x_3152_ = ((size_t)5ULL);
v___x_3153_ = lean_usize_sub(v_x_3141_, v___x_3152_);
v___x_3154_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(v___x_3147_, v___x_3151_, v___x_3153_, v_x_3142_);
v___x_3155_ = lean_unsigned_to_nat(1u);
v___x_3156_ = lean_nat_add(v_j_3146_, v___x_3155_);
lean_dec(v_j_3146_);
v___x_3157_ = lean_array_get_size(v_cs_3143_);
v___x_3158_ = lean_nat_dec_lt(v___x_3156_, v___x_3157_);
if (v___x_3158_ == 0)
{
lean_dec(v___x_3156_);
return v___x_3154_;
}
else
{
size_t v___x_3159_; size_t v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = lean_usize_of_nat(v___x_3156_);
lean_dec(v___x_3156_);
v___x_3160_ = lean_usize_of_nat(v___x_3157_);
v___x_3161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_spec__38(v_cs_3143_, v___x_3159_, v___x_3160_, v___x_3154_);
return v___x_3161_;
}
}
else
{
lean_object* v_vs_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; 
v_vs_3162_ = lean_ctor_get(v_x_3139_, 0);
v___x_3163_ = lean_usize_to_nat(v_x_3140_);
v___x_3164_ = lean_array_get_size(v_vs_3162_);
v___x_3165_ = lean_nat_dec_lt(v___x_3163_, v___x_3164_);
if (v___x_3165_ == 0)
{
lean_dec(v___x_3163_);
return v_x_3142_;
}
else
{
size_t v___x_3166_; size_t v___x_3167_; lean_object* v___x_3168_; 
v___x_3166_ = lean_usize_of_nat(v___x_3163_);
lean_dec(v___x_3163_);
v___x_3167_ = lean_usize_of_nat(v___x_3164_);
v___x_3168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_vs_3162_, v___x_3166_, v___x_3167_, v_x_3142_);
return v___x_3168_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3139_ = stack[0].m_obj;
size_t v_x_3140_ = stack[1].m_num;
size_t v_x_3141_ = stack[2].m_num;
lean_object* v_x_3142_ = stack[3].m_obj;
lean_object* v_res_3169_;
v_res_3169_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(v_x_3139_, v_x_3140_, v_x_3141_, v_x_3142_);
stack->m_obj
 = v_res_3169_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29___boxed(lean_object* v_x_3170_, lean_object* v_x_3171_, lean_object* v_x_3172_, lean_object* v_x_3173_){
_start:
{
size_t v_x_98111__boxed_3174_; size_t v_x_98112__boxed_3175_; lean_object* v_res_3176_; 
v_x_98111__boxed_3174_ = lean_unbox_usize(v_x_3171_);
lean_dec(v_x_3171_);
v_x_98112__boxed_3175_ = lean_unbox_usize(v_x_3172_);
lean_dec(v_x_3172_);
v_res_3176_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(v_x_3170_, v_x_98111__boxed_3174_, v_x_98112__boxed_3175_, v_x_3173_);
lean_dec_ref(v_x_3170_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object* v_t_3177_, lean_object* v_init_3178_, lean_object* v_start_3179_){
_start:
{
lean_object* v___x_3180_; uint8_t v___x_3181_; 
v___x_3180_ = lean_unsigned_to_nat(0u);
v___x_3181_ = lean_nat_dec_eq(v_start_3179_, v___x_3180_);
if (v___x_3181_ == 0)
{
lean_object* v_root_3182_; lean_object* v_tail_3183_; size_t v_shift_3184_; lean_object* v_tailOff_3185_; uint8_t v___x_3186_; 
v_root_3182_ = lean_ctor_get(v_t_3177_, 0);
v_tail_3183_ = lean_ctor_get(v_t_3177_, 1);
v_shift_3184_ = lean_ctor_get_usize(v_t_3177_, 4);
v_tailOff_3185_ = lean_ctor_get(v_t_3177_, 3);
v___x_3186_ = lean_nat_dec_le(v_tailOff_3185_, v_start_3179_);
if (v___x_3186_ == 0)
{
size_t v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; uint8_t v___x_3190_; 
v___x_3187_ = lean_usize_of_nat(v_start_3179_);
v___x_3188_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__29(v_root_3182_, v___x_3187_, v_shift_3184_, v_init_3178_);
v___x_3189_ = lean_array_get_size(v_tail_3183_);
v___x_3190_ = lean_nat_dec_lt(v___x_3180_, v___x_3189_);
if (v___x_3190_ == 0)
{
return v___x_3188_;
}
else
{
size_t v___x_3191_; size_t v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = ((size_t)0ULL);
v___x_3192_ = lean_usize_of_nat(v___x_3189_);
v___x_3193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_tail_3183_, v___x_3191_, v___x_3192_, v___x_3188_);
return v___x_3193_;
}
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; uint8_t v___x_3196_; 
v___x_3194_ = lean_nat_sub(v_start_3179_, v_tailOff_3185_);
v___x_3195_ = lean_array_get_size(v_tail_3183_);
v___x_3196_ = lean_nat_dec_lt(v___x_3194_, v___x_3195_);
if (v___x_3196_ == 0)
{
lean_dec(v___x_3194_);
return v_init_3178_;
}
else
{
size_t v___x_3197_; size_t v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = lean_usize_of_nat(v___x_3194_);
lean_dec(v___x_3194_);
v___x_3198_ = lean_usize_of_nat(v___x_3195_);
v___x_3199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_tail_3183_, v___x_3197_, v___x_3198_, v_init_3178_);
return v___x_3199_;
}
}
}
else
{
lean_object* v_root_3200_; lean_object* v_tail_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; 
v_root_3200_ = lean_ctor_get(v_t_3177_, 0);
v_tail_3201_ = lean_ctor_get(v_t_3177_, 1);
v___x_3202_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__31(v_root_3200_, v_init_3178_);
v___x_3203_ = lean_array_get_size(v_tail_3201_);
v___x_3204_ = lean_nat_dec_lt(v___x_3180_, v___x_3203_);
if (v___x_3204_ == 0)
{
return v___x_3202_;
}
else
{
size_t v___x_3205_; size_t v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = ((size_t)0ULL);
v___x_3206_ = lean_usize_of_nat(v___x_3203_);
v___x_3207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12_spec__30(v_tail_3201_, v___x_3205_, v___x_3206_, v___x_3202_);
return v___x_3207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object* v_t_3208_, lean_object* v_init_3209_, lean_object* v_start_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v_t_3208_, v_init_3209_, v_start_3210_);
lean_dec(v_start_3210_);
lean_dec_ref(v_t_3208_);
return v_res_3211_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(lean_object* v_msgData_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v___x_3218_; lean_object* v_env_3219_; uint8_t v___x_3220_; lean_object* v_env_3221_; lean_object* v___x_3222_; lean_object* v_toCold_3223_; lean_object* v_mctx_3224_; lean_object* v_lctx_3225_; lean_object* v_options_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3218_ = lean_st_ref_get(v___y_3216_);
v_env_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc_ref(v_env_3219_);
lean_dec(v___x_3218_);
v___x_3220_ = 0;
v_env_3221_ = l_Lean_Environment_setRecordingDeps(v_env_3219_, v___x_3220_);
v___x_3222_ = lean_st_ref_get(v___y_3214_);
v_toCold_3223_ = lean_ctor_get(v___y_3215_, 0);
v_mctx_3224_ = lean_ctor_get(v___x_3222_, 0);
lean_inc_ref(v_mctx_3224_);
lean_dec(v___x_3222_);
v_lctx_3225_ = lean_ctor_get(v___y_3213_, 2);
v_options_3226_ = lean_ctor_get(v_toCold_3223_, 2);
lean_inc_ref(v_options_3226_);
lean_inc_ref(v_lctx_3225_);
v___x_3227_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3227_, 0, v_env_3221_);
lean_ctor_set(v___x_3227_, 1, v_mctx_3224_);
lean_ctor_set(v___x_3227_, 2, v_lctx_3225_);
lean_ctor_set(v___x_3227_, 3, v_options_3226_);
v___x_3228_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set(v___x_3228_, 1, v_msgData_3212_);
v___x_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3212_ = stack[0].m_obj;
lean_object* v___y_3213_ = stack[1].m_obj;
lean_object* v___y_3214_ = stack[2].m_obj;
lean_object* v___y_3215_ = stack[3].m_obj;
lean_object* v___y_3216_ = stack[4].m_obj;
lean_object* v_res_3230_;
v_res_3230_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(v_msgData_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
stack->m_obj
 = v_res_3230_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38___boxed(lean_object* v_msgData_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(v_msgData_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
return v_res_3237_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0(void){
_start:
{
lean_object* v___x_3238_; double v___x_3239_; 
v___x_3238_ = lean_unsigned_to_nat(0u);
v___x_3239_ = lean_float_of_nat(v___x_3238_);
return v___x_3239_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(lean_object* v_cls_3243_, lean_object* v_msg_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v_ref_3250_; lean_object* v___x_3251_; lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3297_; 
v_ref_3250_ = lean_ctor_get(v___y_3247_, 2);
v___x_3251_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_spec__38(v_msg_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3254_ = v___x_3251_;
v_isShared_3255_ = v_isSharedCheck_3297_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3297_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; lean_object* v_traceState_3257_; lean_object* v_env_3258_; lean_object* v_nextMacroScope_3259_; lean_object* v_ngen_3260_; lean_object* v_auxDeclNGen_3261_; lean_object* v_cache_3262_; lean_object* v_recordedDeps_3263_; lean_object* v_messages_3264_; lean_object* v_infoState_3265_; lean_object* v_snapshotTasks_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3296_; 
v___x_3256_ = lean_st_ref_take(v___y_3248_);
v_traceState_3257_ = lean_ctor_get(v___x_3256_, 4);
v_env_3258_ = lean_ctor_get(v___x_3256_, 0);
v_nextMacroScope_3259_ = lean_ctor_get(v___x_3256_, 1);
v_ngen_3260_ = lean_ctor_get(v___x_3256_, 2);
v_auxDeclNGen_3261_ = lean_ctor_get(v___x_3256_, 3);
v_cache_3262_ = lean_ctor_get(v___x_3256_, 5);
v_recordedDeps_3263_ = lean_ctor_get(v___x_3256_, 6);
v_messages_3264_ = lean_ctor_get(v___x_3256_, 7);
v_infoState_3265_ = lean_ctor_get(v___x_3256_, 8);
v_snapshotTasks_3266_ = lean_ctor_get(v___x_3256_, 9);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3268_ = v___x_3256_;
v_isShared_3269_ = v_isSharedCheck_3296_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_snapshotTasks_3266_);
lean_inc(v_infoState_3265_);
lean_inc(v_messages_3264_);
lean_inc(v_recordedDeps_3263_);
lean_inc(v_cache_3262_);
lean_inc(v_traceState_3257_);
lean_inc(v_auxDeclNGen_3261_);
lean_inc(v_ngen_3260_);
lean_inc(v_nextMacroScope_3259_);
lean_inc(v_env_3258_);
lean_dec(v___x_3256_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3296_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
uint64_t v_tid_3270_; lean_object* v_traces_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3295_; 
v_tid_3270_ = lean_ctor_get_uint64(v_traceState_3257_, sizeof(void*)*1);
v_traces_3271_ = lean_ctor_get(v_traceState_3257_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_traceState_3257_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3273_ = v_traceState_3257_;
v_isShared_3274_ = v_isSharedCheck_3295_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_traces_3271_);
lean_dec(v_traceState_3257_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3295_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; double v___x_3277_; uint8_t v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3275_ = lean_box(0);
v___x_3276_ = lean_box(0);
v___x_3277_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__0);
v___x_3278_ = 0;
v___x_3279_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__1));
v___x_3280_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3280_, 0, v_cls_3243_);
lean_ctor_set(v___x_3280_, 1, v___x_3276_);
lean_ctor_set(v___x_3280_, 2, v___x_3279_);
lean_ctor_set_float(v___x_3280_, sizeof(void*)*3, v___x_3277_);
lean_ctor_set_float(v___x_3280_, sizeof(void*)*3 + 8, v___x_3277_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*3 + 16, v___x_3278_);
v___x_3281_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___closed__2));
v___x_3282_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v_a_3252_);
lean_ctor_set(v___x_3282_, 2, v___x_3281_);
lean_inc(v_ref_3250_);
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v_ref_3250_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = l_Lean_PersistentArray_push___redArg(v_traces_3271_, v___x_3283_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3284_);
v___x_3286_ = v___x_3273_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3284_);
lean_ctor_set_uint64(v_reuseFailAlloc_3294_, sizeof(void*)*1, v_tid_3270_);
v___x_3286_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
lean_object* v___x_3288_; 
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 4, v___x_3286_);
v___x_3288_ = v___x_3268_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_env_3258_);
lean_ctor_set(v_reuseFailAlloc_3293_, 1, v_nextMacroScope_3259_);
lean_ctor_set(v_reuseFailAlloc_3293_, 2, v_ngen_3260_);
lean_ctor_set(v_reuseFailAlloc_3293_, 3, v_auxDeclNGen_3261_);
lean_ctor_set(v_reuseFailAlloc_3293_, 4, v___x_3286_);
lean_ctor_set(v_reuseFailAlloc_3293_, 5, v_cache_3262_);
lean_ctor_set(v_reuseFailAlloc_3293_, 6, v_recordedDeps_3263_);
lean_ctor_set(v_reuseFailAlloc_3293_, 7, v_messages_3264_);
lean_ctor_set(v_reuseFailAlloc_3293_, 8, v_infoState_3265_);
lean_ctor_set(v_reuseFailAlloc_3293_, 9, v_snapshotTasks_3266_);
v___x_3288_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3291_; 
v___x_3289_ = lean_st_ref_put(v___y_3248_, v___x_3288_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 0, v___x_3275_);
v___x_3291_ = v___x_3254_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3275_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3243_ = stack[0].m_obj;
lean_object* v_msg_3244_ = stack[1].m_obj;
lean_object* v___y_3245_ = stack[2].m_obj;
lean_object* v___y_3246_ = stack[3].m_obj;
lean_object* v___y_3247_ = stack[4].m_obj;
lean_object* v___y_3248_ = stack[5].m_obj;
lean_object* v_res_3298_;
v_res_3298_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v_cls_3243_, v_msg_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
stack->m_obj
 = v_res_3298_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg___boxed(lean_object* v_cls_3299_, lean_object* v_msg_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v_cls_3299_, v_msg_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
return v_res_3306_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2));
v___x_3312_ = l_Lean_stringToMessageData(v___x_3311_);
return v___x_3312_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3326_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10));
v___x_3327_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1));
v___x_3328_ = l_Lean_Name_append(v___x_3327_, v___x_3326_);
return v___x_3328_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13(void){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12));
v___x_3331_ = l_Lean_stringToMessageData(v___x_3330_);
return v___x_3331_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3336_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14));
v___x_3337_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1));
v___x_3338_ = l_Lean_Name_append(v___x_3337_, v___x_3336_);
return v___x_3338_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__16));
v___x_3341_ = l_Lean_stringToMessageData(v___x_3340_);
return v___x_3341_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = l_Lean_instInhabitedExpr;
v___x_3355_ = lean_box(0);
v___x_3356_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3342_, v_a_3350_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3497_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3359_ = v___x_3356_;
v_isShared_3360_ = v_isSharedCheck_3497_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3356_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3497_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_vars_3361_; lean_object* v_varsHistory_3362_; lean_object* v_dvds_3363_; lean_object* v_lowers_3364_; lean_object* v_uppers_3365_; lean_object* v_diseqs_3366_; uint8_t v___x_3367_; 
v_vars_3361_ = lean_ctor_get(v_a_3357_, 0);
lean_inc_ref(v_vars_3361_);
v_varsHistory_3362_ = lean_ctor_get(v_a_3357_, 2);
lean_inc_ref(v_varsHistory_3362_);
v_dvds_3363_ = lean_ctor_get(v_a_3357_, 5);
lean_inc_ref(v_dvds_3363_);
v_lowers_3364_ = lean_ctor_get(v_a_3357_, 6);
lean_inc_ref(v_lowers_3364_);
v_uppers_3365_ = lean_ctor_get(v_a_3357_, 7);
lean_inc_ref(v_uppers_3365_);
v_diseqs_3366_ = lean_ctor_get(v_a_3357_, 8);
lean_inc_ref(v_diseqs_3366_);
lean_dec(v_a_3357_);
v___x_3367_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_3361_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; 
lean_del_object(v___x_3359_);
v___x_3368_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3370_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3369_);
lean_dec_ref_known(v___x_3368_, 1);
v___x_3370_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___redArg(v_a_3369_, v_a_3342_, v_a_3350_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3476_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3373_ = v___x_3370_;
v_isShared_3374_ = v_isSharedCheck_3476_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3370_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3476_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v_size_3375_; lean_object* v___x_3376_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v_options_3388_; lean_object* v_inheritedTraceOptions_3389_; lean_object* v___y_3390_; uint8_t v___x_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; 
v_size_3375_ = lean_ctor_get(v_vars_3361_, 2);
lean_inc(v_size_3375_);
lean_dec_ref(v_vars_3361_);
v___x_3376_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_a_3371_);
v___x_3403_ = l_Lean_PersistentArray_isEmpty___redArg(v_varsHistory_3362_);
v___x_3404_ = l_List_range(v_size_3375_);
v___x_3405_ = l_List_any___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(v___x_3403_, v_a_3369_, v___x_3376_, v___x_3367_, v___x_3404_);
lean_dec(v___x_3404_);
lean_dec(v_a_3369_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; lean_object* v___x_3408_; 
lean_dec_ref(v___x_3376_);
lean_dec(v_a_3371_);
lean_dec_ref(v_diseqs_3366_);
lean_dec_ref(v_uppers_3365_);
lean_dec_ref(v_lowers_3364_);
lean_dec_ref(v_dvds_3363_);
lean_dec_ref(v_varsHistory_3362_);
v___x_3406_ = lean_box(0);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3406_);
v___x_3408_ = v___x_3373_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
else
{
lean_object* v_toCold_3410_; lean_object* v_options_3411_; lean_object* v_inheritedTraceOptions_3412_; uint8_t v_hasTrace_3413_; lean_object* v___f_3414_; lean_object* v___f_3415_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; 
lean_del_object(v___x_3373_);
v_toCold_3410_ = lean_ctor_get(v_a_3350_, 0);
v_options_3411_ = lean_ctor_get(v_toCold_3410_, 2);
v_inheritedTraceOptions_3412_ = lean_ctor_get(v_toCold_3410_, 11);
v_hasTrace_3413_ = lean_ctor_get_uint8(v_options_3411_, sizeof(void*)*1);
lean_inc_ref_n(v___x_3376_, 2);
v___f_3414_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3414_, 0, v___x_3353_);
lean_closure_set(v___f_3414_, 1, v___x_3376_);
lean_inc(v_a_3371_);
v___f_3415_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed), 6, 5);
lean_closure_set(v___f_3415_, 0, v___x_3354_);
lean_closure_set(v___f_3415_, 1, v_a_3371_);
lean_closure_set(v___f_3415_, 2, v___f_3414_);
lean_closure_set(v___f_3415_, 3, v___x_3355_);
lean_closure_set(v___f_3415_, 4, v___x_3376_);
if (v_hasTrace_3413_ == 0)
{
lean_dec_ref(v_varsHistory_3362_);
v___y_3417_ = v_a_3342_;
v___y_3418_ = v_a_3343_;
v___y_3419_ = v_a_3344_;
v___y_3420_ = v_a_3345_;
v___y_3421_ = v_a_3346_;
v___y_3422_ = v_a_3347_;
v___y_3423_ = v_a_3348_;
v___y_3424_ = v_a_3349_;
v___y_3425_ = v_a_3350_;
v___y_3426_ = v_a_3351_;
goto v___jp_3416_;
}
else
{
lean_object* v___x_3464_; lean_object* v___x_3465_; uint8_t v___x_3466_; 
v___x_3464_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__14));
v___x_3465_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__15);
v___x_3466_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3412_, v_options_3411_, v___x_3465_);
if (v___x_3466_ == 0)
{
lean_dec_ref(v_varsHistory_3362_);
v___y_3417_ = v_a_3342_;
v___y_3418_ = v_a_3343_;
v___y_3419_ = v_a_3344_;
v___y_3420_ = v_a_3345_;
v___y_3421_ = v_a_3346_;
v___y_3422_ = v_a_3347_;
v___y_3423_ = v_a_3348_;
v___y_3424_ = v_a_3349_;
v___y_3425_ = v_a_3350_;
v___y_3426_ = v_a_3351_;
goto v___jp_3416_;
}
else
{
lean_object* v_size_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v_size_3467_ = lean_ctor_get(v_varsHistory_3362_, 2);
lean_inc(v_size_3467_);
lean_dec_ref(v_varsHistory_3362_);
v___x_3468_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__17);
v___x_3469_ = lean_unsigned_to_nat(1u);
v___x_3470_ = lean_nat_add(v_size_3467_, v___x_3469_);
lean_dec(v_size_3467_);
v___x_3471_ = l_Nat_reprFast(v___x_3470_);
v___x_3472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
v___x_3473_ = l_Lean_MessageData_ofFormat(v___x_3472_);
v___x_3474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3468_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v___x_3475_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___x_3464_, v___x_3474_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_dec_ref_known(v___x_3475_, 1);
v___y_3417_ = v_a_3342_;
v___y_3418_ = v_a_3343_;
v___y_3419_ = v_a_3344_;
v___y_3420_ = v_a_3345_;
v___y_3421_ = v_a_3346_;
v___y_3422_ = v_a_3347_;
v___y_3423_ = v_a_3348_;
v___y_3424_ = v_a_3349_;
v___y_3425_ = v_a_3350_;
v___y_3426_ = v_a_3351_;
goto v___jp_3416_;
}
else
{
lean_dec_ref(v___f_3415_);
lean_dec_ref(v___x_3376_);
lean_dec(v_a_3371_);
lean_dec_ref(v_diseqs_3366_);
lean_dec_ref(v_uppers_3365_);
lean_dec_ref(v_lowers_3364_);
lean_dec_ref(v_dvds_3363_);
return v___x_3475_;
}
}
}
v___jp_3416_:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v___x_3428_; lean_object* v___x_3429_; size_t v_sz_3430_; size_t v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; size_t v_sz_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; size_t v_sz_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_dec_ref_known(v___x_3427_, 1);
v___x_3428_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7));
v___x_3429_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_dvds_3363_, v___x_3428_, v___x_3353_);
lean_dec_ref(v_dvds_3363_);
v_sz_3430_ = lean_array_size(v___x_3429_);
v___x_3431_ = ((size_t)0ULL);
v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v___x_3376_, v_sz_3430_, v___x_3431_, v___x_3429_);
v___x_3433_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v_lowers_3364_, v___x_3428_, v___x_3353_);
lean_dec_ref(v_lowers_3364_);
v___x_3434_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v_uppers_3365_, v___x_3433_, v___x_3353_);
lean_dec_ref(v_uppers_3365_);
v_sz_3435_ = lean_array_size(v___x_3434_);
v___x_3436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_3376_, v_sz_3435_, v___x_3431_, v___x_3434_);
v___x_3437_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v_diseqs_3366_, v___x_3428_, v___x_3353_);
lean_dec_ref(v_diseqs_3366_);
v_sz_3438_ = lean_array_size(v___x_3437_);
v___x_3439_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v___x_3376_, v_sz_3438_, v___x_3431_, v___x_3437_);
v___x_3440_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3441_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3440_, v___f_3415_, v___y_3417_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v___x_3442_; size_t v_sz_3443_; lean_object* v___x_3444_; 
lean_dec_ref_known(v___x_3441_, 1);
v___x_3442_ = lean_box(0);
v_sz_3443_ = lean_array_size(v___x_3432_);
v___x_3444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_3432_, v_sz_3443_, v___x_3431_, v___x_3442_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec_ref(v___x_3432_);
if (lean_obj_tag(v___x_3444_) == 0)
{
size_t v_sz_3445_; lean_object* v___x_3446_; 
lean_dec_ref_known(v___x_3444_, 1);
v_sz_3445_ = lean_array_size(v___x_3436_);
v___x_3446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v___x_3436_, v_sz_3445_, v___x_3431_, v___x_3442_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec_ref(v___x_3436_);
if (lean_obj_tag(v___x_3446_) == 0)
{
size_t v_sz_3447_; lean_object* v___x_3448_; 
lean_dec_ref_known(v___x_3446_, 1);
v_sz_3447_ = lean_array_size(v___x_3439_);
v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v___x_3439_, v_sz_3447_, v___x_3431_, v___x_3442_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec_ref(v___x_3439_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_toCold_3449_; lean_object* v_options_3450_; uint8_t v_hasTrace_3451_; 
lean_dec_ref_known(v___x_3448_, 1);
v_toCold_3449_ = lean_ctor_get(v___y_3425_, 0);
v_options_3450_ = lean_ctor_get(v_toCold_3449_, 2);
v_hasTrace_3451_ = lean_ctor_get_uint8(v_options_3450_, sizeof(void*)*1);
if (v_hasTrace_3451_ == 0)
{
lean_object* v___x_3452_; 
lean_dec_ref(v___x_3376_);
lean_dec(v_a_3371_);
v___x_3452_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
return v___x_3452_;
}
else
{
lean_object* v_inheritedTraceOptions_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v_inheritedTraceOptions_3453_ = lean_ctor_get(v_toCold_3449_, 11);
v___x_3454_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10));
v___x_3455_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11);
v___x_3456_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3453_, v_options_3450_, v___x_3455_);
if (v___x_3456_ == 0)
{
lean_dec(v_a_3371_);
v___y_3378_ = v___x_3454_;
v___y_3379_ = v___y_3417_;
v___y_3380_ = v___y_3418_;
v___y_3381_ = v___y_3419_;
v___y_3382_ = v___y_3420_;
v___y_3383_ = v___y_3421_;
v___y_3384_ = v___y_3422_;
v___y_3385_ = v___y_3423_;
v___y_3386_ = v___y_3424_;
v___y_3387_ = v___y_3425_;
v_options_3388_ = v_options_3450_;
v_inheritedTraceOptions_3389_ = v_inheritedTraceOptions_3453_;
v___y_3390_ = v___y_3426_;
goto v___jp_3377_;
}
else
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3457_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13);
v___x_3458_ = lean_array_to_list(v_a_3371_);
v___x_3459_ = lean_box(0);
v___x_3460_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(v___x_3458_, v___x_3459_);
v___x_3461_ = l_Lean_MessageData_ofList(v___x_3460_);
v___x_3462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3457_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___x_3454_, v___x_3462_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_dec_ref_known(v___x_3463_, 1);
v___y_3378_ = v___x_3454_;
v___y_3379_ = v___y_3417_;
v___y_3380_ = v___y_3418_;
v___y_3381_ = v___y_3419_;
v___y_3382_ = v___y_3420_;
v___y_3383_ = v___y_3421_;
v___y_3384_ = v___y_3422_;
v___y_3385_ = v___y_3423_;
v___y_3386_ = v___y_3424_;
v___y_3387_ = v___y_3425_;
v_options_3388_ = v_options_3450_;
v_inheritedTraceOptions_3389_ = v_inheritedTraceOptions_3453_;
v___y_3390_ = v___y_3426_;
goto v___jp_3377_;
}
else
{
lean_dec_ref(v___x_3376_);
return v___x_3463_;
}
}
}
}
else
{
lean_dec_ref(v___x_3376_);
lean_dec(v_a_3371_);
return v___x_3448_;
}
}
else
{
lean_dec_ref(v___x_3439_);
lean_dec_ref(v___x_3376_);
lean_dec(v_a_3371_);
return v___x_3446_;
}
}
else
{
lean_dec_ref(v___x_3439_);
lean_dec_ref(v___x_3436_);
lean_dec_ref(v___x_3376_);
lean_dec(v_a_3371_);
return v___x_3444_;
}
}
else
{
lean_dec_ref(v___x_3439_);
lean_dec_ref(v___x_3436_);
lean_dec_ref(v___x_3432_);
lean_dec_ref(v___x_3376_);
lean_dec(v_a_3371_);
return v___x_3441_;
}
}
else
{
lean_dec_ref(v___f_3415_);
lean_dec_ref(v___x_3376_);
lean_dec(v_a_3371_);
lean_dec_ref(v_diseqs_3366_);
lean_dec_ref(v_uppers_3365_);
lean_dec_ref(v_lowers_3364_);
lean_dec_ref(v_dvds_3363_);
return v___x_3427_;
}
}
}
v___jp_3377_:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; 
v___x_3391_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1));
lean_inc(v___y_3378_);
v___x_3392_ = l_Lean_Name_append(v___x_3391_, v___y_3378_);
v___x_3393_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3389_, v_options_3388_, v___x_3392_);
lean_dec(v___x_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; 
lean_dec(v___y_3378_);
lean_dec_ref(v___x_3376_);
v___x_3394_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3390_);
return v___x_3394_;
}
else
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3395_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3);
v___x_3396_ = lean_array_to_list(v___x_3376_);
v___x_3397_ = lean_box(0);
v___x_3398_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(v___x_3396_, v___x_3397_);
v___x_3399_ = l_Lean_MessageData_ofList(v___x_3398_);
v___x_3400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3395_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
v___x_3401_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v___y_3378_, v___x_3400_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3390_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v___x_3402_; 
lean_dec_ref_known(v___x_3401_, 1);
v___x_3402_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3390_);
return v___x_3402_;
}
else
{
return v___x_3401_;
}
}
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec(v_a_3369_);
lean_dec_ref(v_diseqs_3366_);
lean_dec_ref(v_uppers_3365_);
lean_dec_ref(v_lowers_3364_);
lean_dec_ref(v_dvds_3363_);
lean_dec_ref(v_varsHistory_3362_);
lean_dec_ref(v_vars_3361_);
v_a_3477_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3370_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3370_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v_diseqs_3366_);
lean_dec_ref(v_uppers_3365_);
lean_dec_ref(v_lowers_3364_);
lean_dec_ref(v_dvds_3363_);
lean_dec_ref(v_varsHistory_3362_);
lean_dec_ref(v_vars_3361_);
v_a_3485_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3368_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3368_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3495_; 
lean_dec_ref(v_diseqs_3366_);
lean_dec_ref(v_uppers_3365_);
lean_dec_ref(v_lowers_3364_);
lean_dec_ref(v_dvds_3363_);
lean_dec_ref(v_varsHistory_3362_);
lean_dec_ref(v_vars_3361_);
v___x_3493_ = lean_box(0);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3493_);
v___x_3495_ = v___x_3359_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
v_a_3498_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3356_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3356_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_reorderVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3342_ = stack[0].m_obj;
lean_object* v_a_3343_ = stack[1].m_obj;
lean_object* v_a_3344_ = stack[2].m_obj;
lean_object* v_a_3345_ = stack[3].m_obj;
lean_object* v_a_3346_ = stack[4].m_obj;
lean_object* v_a_3347_ = stack[5].m_obj;
lean_object* v_a_3348_ = stack[6].m_obj;
lean_object* v_a_3349_ = stack[7].m_obj;
lean_object* v_a_3350_ = stack[8].m_obj;
lean_object* v_a_3351_ = stack[9].m_obj;
lean_object* v_res_3506_;
v_res_3506_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
stack->m_obj
 = v_res_3506_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
lean_dec(v_a_3514_);
lean_dec_ref(v_a_3513_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
lean_dec(v_a_3510_);
lean_dec_ref(v_a_3509_);
lean_dec(v_a_3508_);
lean_dec(v_a_3507_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object* v_00_u03b2_3519_, lean_object* v_00_u03c3_3520_, lean_object* v_pm_3521_, lean_object* v_f_3522_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1___redArg(v_pm_3521_, v_f_3522_);
return v___x_3523_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(lean_object* v_cls_3524_, lean_object* v_msg_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___redArg(v_cls_3524_, v_msg_3525_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
return v___x_3537_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3524_ = stack[0].m_obj;
lean_object* v_msg_3525_ = stack[1].m_obj;
lean_object* v___y_3526_ = stack[2].m_obj;
lean_object* v___y_3527_ = stack[3].m_obj;
lean_object* v___y_3528_ = stack[4].m_obj;
lean_object* v___y_3529_ = stack[5].m_obj;
lean_object* v___y_3530_ = stack[6].m_obj;
lean_object* v___y_3531_ = stack[7].m_obj;
lean_object* v___y_3532_ = stack[8].m_obj;
lean_object* v___y_3533_ = stack[9].m_obj;
lean_object* v___y_3534_ = stack[10].m_obj;
lean_object* v___y_3535_ = stack[11].m_obj;
lean_object* v_res_3538_;
v_res_3538_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(v_cls_3524_, v_msg_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
stack->m_obj
 = v_res_3538_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18___boxed(lean_object* v_cls_3539_, lean_object* v_msg_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__18(v_cls_3539_, v_msg_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec(v___y_3541_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1___redArg(lean_object* v_pm_3553_, lean_object* v_f_3554_){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v_f_3554_, v_pm_3553_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1(lean_object* v_00_u03b2_3556_, lean_object* v_00_u03c3_3557_, lean_object* v_pm_3558_, lean_object* v_f_3559_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v_f_3559_, v_pm_3558_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_3561_, lean_object* v_00_u03b2_3562_, lean_object* v_00_u03c3_3563_, lean_object* v_f_3564_, lean_object* v_n_3565_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2___redArg(v_f_3564_, v_n_3565_);
return v___x_3566_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21(lean_object* v_00_u03b1_3567_, lean_object* v_00_u03b2_3568_, lean_object* v_00_u03c3_3569_, lean_object* v_f_3570_, size_t v_sz_3571_, size_t v_i_3572_, lean_object* v_bs_3573_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___redArg(v_f_3570_, v_sz_3571_, v_i_3572_, v_bs_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3570_ = stack[3].m_obj;
size_t v_sz_3571_ = stack[4].m_num;
size_t v_i_3572_ = stack[5].m_num;
lean_object* v_bs_3573_ = stack[6].m_obj;
lean_object* v_res_3575_;
v_res_3575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21(lean_box(0), lean_box(0), lean_box(0), v_f_3570_, v_sz_3571_, v_i_3572_, v_bs_3573_);
stack->m_obj
 = v_res_3575_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21___boxed(lean_object* v_00_u03b1_3576_, lean_object* v_00_u03b2_3577_, lean_object* v_00_u03c3_3578_, lean_object* v_f_3579_, lean_object* v_sz_3580_, lean_object* v_i_3581_, lean_object* v_bs_3582_){
_start:
{
size_t v_sz_boxed_3583_; size_t v_i_boxed_3584_; lean_object* v_res_3585_; 
v_sz_boxed_3583_ = lean_unbox_usize(v_sz_3580_);
lean_dec(v_sz_3580_);
v_i_boxed_3584_ = lean_unbox_usize(v_i_3581_);
lean_dec(v_i_3581_);
v_res_3585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__21(v_00_u03b1_3576_, v_00_u03b2_3577_, v_00_u03c3_3578_, v_f_3579_, v_sz_boxed_3583_, v_i_boxed_3584_, v_bs_3582_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22(lean_object* v_00_u03b1_3586_, lean_object* v_00_u03b2_3587_, lean_object* v_f_3588_, lean_object* v_as_3589_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___redArg(v_f_3588_, v_as_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22___boxed(lean_object* v_00_u03b1_3591_, lean_object* v_00_u03b2_3592_, lean_object* v_f_3593_, lean_object* v_as_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22(v_00_u03b1_3591_, v_00_u03b2_3592_, v_f_3593_, v_as_3594_);
lean_dec_ref(v_as_3594_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42(lean_object* v_00_u03b1_3596_, lean_object* v_00_u03b2_3597_, lean_object* v_f_3598_, lean_object* v_as_3599_, lean_object* v_i_3600_, lean_object* v_acc_3601_, lean_object* v_hle_3602_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___redArg(v_f_3598_, v_as_3599_, v_i_3600_, v_acc_3601_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42___boxed(lean_object* v_00_u03b1_3604_, lean_object* v_00_u03b2_3605_, lean_object* v_f_3606_, lean_object* v_as_3607_, lean_object* v_i_3608_, lean_object* v_acc_3609_, lean_object* v_hle_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__1_spec__2_spec__22_spec__42(v_00_u03b1_3604_, v_00_u03b2_3605_, v_f_3606_, v_as_3607_, v_i_3608_, v_acc_3609_, v_hle_3610_);
lean_dec_ref(v_as_3607_);
return v_res_3611_;
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
