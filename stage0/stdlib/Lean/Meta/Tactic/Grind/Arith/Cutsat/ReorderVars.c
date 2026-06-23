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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Int_Linear_instBEqPoly_beq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Int_Linear_Poly_reorder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_reorder___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "search"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reorder"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value),LEAN_SCALAR_PTR_LITERAL(236, 159, 191, 181, 87, 7, 198, 44)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "old2new: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "new2old: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg___boxed(lean_object* v_a_33_, lean_object* v_x_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_33_, v_x_34_, v_a_35_);
lean_dec(v_x_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(lean_object* v_a_38_, lean_object* v_x_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_38_, v_x_39_, v_a_40_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___boxed(lean_object* v_a_53_, lean_object* v_x_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(v_a_53_, v_x_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec(v_a_56_);
lean_dec(v_x_54_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(lean_object* v_a_68_, lean_object* v_x_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; lean_object* v___y_74_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_72_ = lean_box(0);
v___x_77_ = lean_array_get_size(v_a_70_);
v___x_78_ = lean_nat_dec_lt(v_x_69_, v___x_77_);
if (v___x_78_ == 0)
{
lean_dec(v_a_68_);
v___y_74_ = v_a_70_;
goto v___jp_73_;
}
else
{
lean_object* v_v_79_; lean_object* v_maxLowerCoeff_80_; lean_object* v_maxUpperCoeff_81_; lean_object* v_maxDvdCoeff_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_94_; 
v_v_79_ = lean_array_fget(v_a_70_, v_x_69_);
v_maxLowerCoeff_80_ = lean_ctor_get(v_v_79_, 0);
v_maxUpperCoeff_81_ = lean_ctor_get(v_v_79_, 1);
v_maxDvdCoeff_82_ = lean_ctor_get(v_v_79_, 2);
v_isSharedCheck_94_ = !lean_is_exclusive(v_v_79_);
if (v_isSharedCheck_94_ == 0)
{
v___x_84_ = v_v_79_;
v_isShared_85_ = v_isSharedCheck_94_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_maxDvdCoeff_82_);
lean_inc(v_maxUpperCoeff_81_);
lean_inc(v_maxLowerCoeff_80_);
lean_dec(v_v_79_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_94_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v_xs_x27_86_; lean_object* v___y_88_; uint8_t v___x_93_; 
v_xs_x27_86_ = lean_array_fset(v_a_70_, v_x_69_, v___x_72_);
v___x_93_ = lean_nat_dec_le(v_a_68_, v_maxUpperCoeff_81_);
if (v___x_93_ == 0)
{
lean_dec(v_maxUpperCoeff_81_);
v___y_88_ = v_a_68_;
goto v___jp_87_;
}
else
{
lean_dec(v_a_68_);
v___y_88_ = v_maxUpperCoeff_81_;
goto v___jp_87_;
}
v___jp_87_:
{
lean_object* v___x_90_; 
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___y_88_);
v___x_90_ = v___x_84_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_maxLowerCoeff_80_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___y_88_);
lean_ctor_set(v_reuseFailAlloc_92_, 2, v_maxDvdCoeff_82_);
v___x_90_ = v_reuseFailAlloc_92_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; 
v___x_91_ = lean_array_fset(v_xs_x27_86_, v_x_69_, v___x_90_);
v___y_74_ = v___x_91_;
goto v___jp_73_;
}
}
}
}
v___jp_73_:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_72_);
lean_ctor_set(v___x_75_, 1, v___y_74_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg___boxed(lean_object* v_a_95_, lean_object* v_x_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_95_, v_x_96_, v_a_97_);
lean_dec(v_x_96_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(lean_object* v_a_100_, lean_object* v_x_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_100_, v_x_101_, v_a_102_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___boxed(lean_object* v_a_115_, lean_object* v_x_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(v_a_115_, v_x_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec(v_a_118_);
lean_dec(v_x_116_);
return v_res_129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(lean_object* v_a_132_, lean_object* v_x_133_, lean_object* v_a_134_){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0);
v___x_137_ = lean_int_dec_lt(v_a_132_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_nat_abs(v_a_132_);
v___x_139_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v___x_138_, v_x_133_, v_a_134_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_nat_abs(v_a_132_);
v___x_141_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v___x_140_, v_x_133_, v_a_134_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___boxed(lean_object* v_a_142_, lean_object* v_x_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_142_, v_x_143_, v_a_144_);
lean_dec(v_x_143_);
lean_dec(v_a_142_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(lean_object* v_a_147_, lean_object* v_x_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_147_, v_x_148_, v_a_149_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___boxed(lean_object* v_a_162_, lean_object* v_x_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(v_a_162_, v_x_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec(v_a_165_);
lean_dec(v_x_163_);
lean_dec(v_a_162_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(lean_object* v_a_177_, lean_object* v_x_178_, lean_object* v_a_179_){
_start:
{
lean_object* v___x_181_; lean_object* v___y_183_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_181_ = lean_box(0);
v___x_186_ = lean_array_get_size(v_a_179_);
v___x_187_ = lean_nat_dec_lt(v_x_178_, v___x_186_);
if (v___x_187_ == 0)
{
lean_dec(v_a_177_);
v___y_183_ = v_a_179_;
goto v___jp_182_;
}
else
{
lean_object* v_v_188_; lean_object* v_maxLowerCoeff_189_; lean_object* v_maxUpperCoeff_190_; lean_object* v_maxDvdCoeff_191_; lean_object* v_xs_x27_192_; uint8_t v___x_193_; 
v_v_188_ = lean_array_fget(v_a_179_, v_x_178_);
v_maxLowerCoeff_189_ = lean_ctor_get(v_v_188_, 0);
v_maxUpperCoeff_190_ = lean_ctor_get(v_v_188_, 1);
v_maxDvdCoeff_191_ = lean_ctor_get(v_v_188_, 2);
v_xs_x27_192_ = lean_array_fset(v_a_179_, v_x_178_, v___x_181_);
v___x_193_ = lean_nat_dec_le(v_a_177_, v_maxDvdCoeff_191_);
if (v___x_193_ == 0)
{
lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_201_; 
lean_inc(v_maxUpperCoeff_190_);
lean_inc(v_maxLowerCoeff_189_);
v_isSharedCheck_201_ = !lean_is_exclusive(v_v_188_);
if (v_isSharedCheck_201_ == 0)
{
lean_object* v_unused_202_; lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_202_ = lean_ctor_get(v_v_188_, 2);
lean_dec(v_unused_202_);
v_unused_203_ = lean_ctor_get(v_v_188_, 1);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_v_188_, 0);
lean_dec(v_unused_204_);
v___x_195_ = v_v_188_;
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
else
{
lean_dec(v_v_188_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 2, v_a_177_);
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_maxLowerCoeff_189_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_maxUpperCoeff_190_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_a_177_);
v___x_198_ = v_reuseFailAlloc_200_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; 
v___x_199_ = lean_array_fset(v_xs_x27_192_, v_x_178_, v___x_198_);
v___y_183_ = v___x_199_;
goto v___jp_182_;
}
}
}
else
{
lean_object* v___x_205_; 
lean_dec(v_a_177_);
v___x_205_ = lean_array_fset(v_xs_x27_192_, v_x_178_, v_v_188_);
v___y_183_ = v___x_205_;
goto v___jp_182_;
}
}
v___jp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_181_);
lean_ctor_set(v___x_184_, 1, v___y_183_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg___boxed(lean_object* v_a_206_, lean_object* v_x_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_206_, v_x_207_, v_a_208_);
lean_dec(v_x_207_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(lean_object* v_a_211_, lean_object* v_x_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_211_, v_x_212_, v_a_213_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___boxed(lean_object* v_a_226_, lean_object* v_x_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(v_a_226_, v_x_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec(v_a_229_);
lean_dec(v_x_227_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
if (lean_obj_tag(v_a_241_) == 0)
{
lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_252_; 
v_isSharedCheck_252_ = !lean_is_exclusive(v_a_241_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v_a_241_, 0);
lean_dec(v_unused_253_);
v___x_245_ = v_a_241_;
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
else
{
lean_dec(v_a_241_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_a_242_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_248_);
v___x_250_ = v___x_245_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
else
{
lean_object* v_k_254_; lean_object* v_v_255_; lean_object* v_p_256_; lean_object* v___x_257_; lean_object* v_a_258_; lean_object* v_snd_259_; 
v_k_254_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_k_254_);
v_v_255_ = lean_ctor_get(v_a_241_, 1);
lean_inc(v_v_255_);
v_p_256_ = lean_ctor_get(v_a_241_, 2);
lean_inc_ref(v_p_256_);
lean_dec_ref_known(v_a_241_, 3);
v___x_257_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_k_254_, v_v_255_, v_a_242_);
lean_dec(v_v_255_);
lean_dec(v_k_254_);
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref(v___x_257_);
v_snd_259_ = lean_ctor_get(v_a_258_, 1);
lean_inc(v_snd_259_);
lean_dec(v_a_258_);
v_a_241_ = v_p_256_;
v_a_242_ = v_snd_259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg___boxed(lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_261_, v_a_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_265_, v_a_266_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___boxed(lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec(v_a_281_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(lean_object* v_as_296_, size_t v_sz_297_, size_t v_i_298_, lean_object* v_b_299_, lean_object* v___y_300_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = lean_usize_dec_lt(v_i_298_, v_sz_297_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_b_299_);
lean_ctor_set(v___x_303_, 1, v___y_300_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v_a_305_; lean_object* v_p_306_; lean_object* v___x_307_; 
lean_dec_ref(v_b_299_);
v_a_305_ = lean_array_uget_borrowed(v_as_296_, v_i_298_);
v_p_306_ = lean_ctor_get(v_a_305_, 0);
lean_inc_ref(v_p_306_);
v___x_307_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_306_, v___y_300_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v_snd_309_; lean_object* v___x_310_; size_t v___x_311_; size_t v___x_312_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v_snd_309_ = lean_ctor_get(v_a_308_, 1);
lean_inc(v_snd_309_);
lean_dec(v_a_308_);
v___x_310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_add(v_i_298_, v___x_311_);
v_i_298_ = v___x_312_;
v_b_299_ = v___x_310_;
v___y_300_ = v_snd_309_;
goto _start;
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_a_314_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_307_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_307_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_322_, lean_object* v_sz_323_, lean_object* v_i_324_, lean_object* v_b_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
size_t v_sz_boxed_328_; size_t v_i_boxed_329_; lean_object* v_res_330_; 
v_sz_boxed_328_ = lean_unbox_usize(v_sz_323_);
lean_dec(v_sz_323_);
v_i_boxed_329_ = lean_unbox_usize(v_i_324_);
lean_dec(v_i_324_);
v_res_330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_322_, v_sz_boxed_328_, v_i_boxed_329_, v_b_325_, v___y_326_);
lean_dec_ref(v_as_322_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(lean_object* v_as_331_, size_t v_sz_332_, size_t v_i_333_, lean_object* v_b_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = lean_usize_dec_lt(v_i_333_, v_sz_332_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v_b_334_);
lean_ctor_set(v___x_348_, 1, v___y_335_);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
else
{
lean_object* v_a_350_; lean_object* v_p_351_; lean_object* v___x_352_; 
lean_dec_ref(v_b_334_);
v_a_350_ = lean_array_uget_borrowed(v_as_331_, v_i_333_);
v_p_351_ = lean_ctor_get(v_a_350_, 0);
lean_inc_ref(v_p_351_);
v___x_352_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_351_, v___y_335_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v_snd_354_; lean_object* v___x_355_; size_t v___x_356_; size_t v___x_357_; lean_object* v___x_358_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_352_, 1);
v_snd_354_ = lean_ctor_get(v_a_353_, 1);
lean_inc(v_snd_354_);
lean_dec(v_a_353_);
v___x_355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_add(v_i_333_, v___x_356_);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_331_, v_sz_332_, v___x_357_, v___x_355_, v_snd_354_);
return v___x_358_;
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_359_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_352_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_352_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1___boxed(lean_object* v_as_367_, lean_object* v_sz_368_, lean_object* v_i_369_, lean_object* v_b_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
size_t v_sz_boxed_383_; size_t v_i_boxed_384_; lean_object* v_res_385_; 
v_sz_boxed_383_ = lean_unbox_usize(v_sz_368_);
lean_dec(v_sz_368_);
v_i_boxed_384_ = lean_unbox_usize(v_i_369_);
lean_dec(v_i_369_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_as_367_, v_sz_boxed_383_, v_i_boxed_384_, v_b_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v_as_367_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_as_389_, size_t v_sz_390_, size_t v_i_391_, lean_object* v_b_392_, lean_object* v___y_393_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_lt(v_i_391_, v_sz_390_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v_b_392_);
lean_ctor_set(v___x_396_, 1, v___y_393_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
else
{
lean_object* v_a_398_; lean_object* v_p_399_; lean_object* v___x_400_; 
lean_dec_ref(v_b_392_);
v_a_398_ = lean_array_uget_borrowed(v_as_389_, v_i_391_);
v_p_399_ = lean_ctor_get(v_a_398_, 0);
lean_inc_ref(v_p_399_);
v___x_400_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_399_, v___y_393_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v_snd_402_; lean_object* v___x_403_; size_t v___x_404_; size_t v___x_405_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_400_, 1);
v_snd_402_ = lean_ctor_get(v_a_401_, 1);
lean_inc(v_snd_402_);
lean_dec(v_a_401_);
v___x_403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_404_ = ((size_t)1ULL);
v___x_405_ = lean_usize_add(v_i_391_, v___x_404_);
v_i_391_ = v___x_405_;
v_b_392_ = v___x_403_;
v___y_393_ = v_snd_402_;
goto _start;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_400_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_400_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_as_415_, lean_object* v_sz_416_, lean_object* v_i_417_, lean_object* v_b_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
size_t v_sz_boxed_421_; size_t v_i_boxed_422_; lean_object* v_res_423_; 
v_sz_boxed_421_ = lean_unbox_usize(v_sz_416_);
lean_dec(v_sz_416_);
v_i_boxed_422_ = lean_unbox_usize(v_i_417_);
lean_dec(v_i_417_);
v_res_423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_415_, v_sz_boxed_421_, v_i_boxed_422_, v_b_418_, v___y_419_);
lean_dec_ref(v_as_415_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(lean_object* v_as_424_, size_t v_sz_425_, size_t v_i_426_, lean_object* v_b_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = lean_usize_dec_lt(v_i_426_, v_sz_425_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v_b_427_);
lean_ctor_set(v___x_441_, 1, v___y_428_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
else
{
lean_object* v_a_443_; lean_object* v_p_444_; lean_object* v___x_445_; 
lean_dec_ref(v_b_427_);
v_a_443_ = lean_array_uget_borrowed(v_as_424_, v_i_426_);
v_p_444_ = lean_ctor_get(v_a_443_, 0);
lean_inc_ref(v_p_444_);
v___x_445_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_444_, v___y_428_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v_snd_447_; lean_object* v___x_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v___x_445_, 1);
v_snd_447_ = lean_ctor_get(v_a_446_, 1);
lean_inc(v_snd_447_);
lean_dec(v_a_446_);
v___x_448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0));
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_426_, v___x_449_);
v___x_451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_424_, v_sz_425_, v___x_450_, v___x_448_, v_snd_447_);
return v___x_451_;
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_a_452_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_445_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_445_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2___boxed(lean_object* v_as_460_, lean_object* v_sz_461_, lean_object* v_i_462_, lean_object* v_b_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
size_t v_sz_boxed_476_; size_t v_i_boxed_477_; lean_object* v_res_478_; 
v_sz_boxed_476_ = lean_unbox_usize(v_sz_461_);
lean_dec(v_sz_461_);
v_i_boxed_477_ = lean_unbox_usize(v_i_462_);
lean_dec(v_i_462_);
v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_as_460_, v_sz_boxed_476_, v_i_boxed_477_, v_b_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v_as_460_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(lean_object* v_init_479_, lean_object* v_n_480_, lean_object* v_b_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
if (lean_obj_tag(v_n_480_) == 0)
{
lean_object* v_cs_494_; lean_object* v___x_495_; lean_object* v___x_496_; size_t v_sz_497_; size_t v___x_498_; lean_object* v___x_499_; 
v_cs_494_ = lean_ctor_get(v_n_480_, 0);
v___x_495_ = lean_box(0);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v_b_481_);
v_sz_497_ = lean_array_size(v_cs_494_);
v___x_498_ = ((size_t)0ULL);
v___x_499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_479_, v_cs_494_, v_sz_497_, v___x_498_, v___x_496_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_534_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_534_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_534_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_534_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_fst_504_; lean_object* v_fst_505_; 
v_fst_504_ = lean_ctor_get(v_a_500_, 0);
lean_inc(v_fst_504_);
v_fst_505_ = lean_ctor_get(v_fst_504_, 0);
if (lean_obj_tag(v_fst_505_) == 0)
{
lean_object* v_snd_506_; lean_object* v_snd_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_518_; 
v_snd_506_ = lean_ctor_get(v_a_500_, 1);
lean_inc(v_snd_506_);
lean_dec(v_a_500_);
v_snd_507_ = lean_ctor_get(v_fst_504_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_fst_504_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_fst_504_, 0);
lean_dec(v_unused_519_);
v___x_509_ = v_fst_504_;
v_isShared_510_ = v_isSharedCheck_518_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snd_507_);
lean_dec(v_fst_504_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_518_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v_snd_507_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v_snd_506_);
lean_ctor_set(v___x_509_, 0, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_snd_506_);
v___x_513_ = v_reuseFailAlloc_517_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_513_);
v___x_515_ = v___x_502_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_531_; 
lean_inc_ref(v_fst_505_);
v_isSharedCheck_531_ = !lean_is_exclusive(v_fst_504_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; lean_object* v_unused_533_; 
v_unused_532_ = lean_ctor_get(v_fst_504_, 1);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_fst_504_, 0);
lean_dec(v_unused_533_);
v___x_521_ = v_fst_504_;
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
else
{
lean_dec(v_fst_504_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v_snd_523_; lean_object* v_val_524_; lean_object* v___x_526_; 
v_snd_523_ = lean_ctor_get(v_a_500_, 1);
lean_inc(v_snd_523_);
lean_dec(v_a_500_);
v_val_524_ = lean_ctor_get(v_fst_505_, 0);
lean_inc(v_val_524_);
lean_dec_ref_known(v_fst_505_, 1);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v_snd_523_);
lean_ctor_set(v___x_521_, 0, v_val_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_val_524_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_snd_523_);
v___x_526_ = v_reuseFailAlloc_530_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_528_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_526_);
v___x_528_ = v___x_502_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
v_a_535_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_499_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_499_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
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
else
{
lean_object* v_vs_543_; lean_object* v___x_544_; lean_object* v___x_545_; size_t v_sz_546_; size_t v___x_547_; lean_object* v___x_548_; 
v_vs_543_ = lean_ctor_get(v_n_480_, 0);
v___x_544_ = lean_box(0);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v_b_481_);
v_sz_546_ = lean_array_size(v_vs_543_);
v___x_547_ = ((size_t)0ULL);
v___x_548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_vs_543_, v_sz_546_, v___x_547_, v___x_545_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_583_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_583_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_583_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_583_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v_fst_553_; lean_object* v_fst_554_; 
v_fst_553_ = lean_ctor_get(v_a_549_, 0);
lean_inc(v_fst_553_);
v_fst_554_ = lean_ctor_get(v_fst_553_, 0);
if (lean_obj_tag(v_fst_554_) == 0)
{
lean_object* v_snd_555_; lean_object* v_snd_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_567_; 
v_snd_555_ = lean_ctor_get(v_a_549_, 1);
lean_inc(v_snd_555_);
lean_dec(v_a_549_);
v_snd_556_ = lean_ctor_get(v_fst_553_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_fst_553_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v_fst_553_, 0);
lean_dec(v_unused_568_);
v___x_558_ = v_fst_553_;
v_isShared_559_ = v_isSharedCheck_567_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_snd_556_);
lean_dec(v_fst_553_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_567_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v_snd_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v_snd_555_);
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_snd_555_);
v___x_562_ = v_reuseFailAlloc_566_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_564_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_562_);
v___x_564_ = v___x_551_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
else
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_580_; 
lean_inc_ref(v_fst_554_);
v_isSharedCheck_580_ = !lean_is_exclusive(v_fst_553_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; lean_object* v_unused_582_; 
v_unused_581_ = lean_ctor_get(v_fst_553_, 1);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_fst_553_, 0);
lean_dec(v_unused_582_);
v___x_570_ = v_fst_553_;
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
else
{
lean_dec(v_fst_553_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_snd_572_; lean_object* v_val_573_; lean_object* v___x_575_; 
v_snd_572_ = lean_ctor_get(v_a_549_, 1);
lean_inc(v_snd_572_);
lean_dec(v_a_549_);
v_val_573_ = lean_ctor_get(v_fst_554_, 0);
lean_inc(v_val_573_);
lean_dec_ref_known(v_fst_554_, 1);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v_snd_572_);
lean_ctor_set(v___x_570_, 0, v_val_573_);
v___x_575_ = v___x_570_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_val_573_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_snd_572_);
v___x_575_ = v_reuseFailAlloc_579_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_577_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_575_);
v___x_577_ = v___x_551_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
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
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_a_584_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_548_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_548_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(lean_object* v_init_592_, lean_object* v_as_593_, size_t v_sz_594_, size_t v_i_595_, lean_object* v_b_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = lean_usize_dec_lt(v_i_595_, v_sz_594_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v_b_596_);
lean_ctor_set(v___x_610_, 1, v___y_597_);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
else
{
lean_object* v_snd_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_662_; 
v_snd_612_ = lean_ctor_get(v_b_596_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_b_596_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v_b_596_, 0);
lean_dec(v_unused_663_);
v___x_614_ = v_b_596_;
v_isShared_615_ = v_isSharedCheck_662_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_snd_612_);
lean_dec(v_b_596_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_662_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_a_616_; lean_object* v___x_617_; 
v_a_616_ = lean_array_uget_borrowed(v_as_593_, v_i_595_);
lean_inc(v_snd_612_);
v___x_617_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_592_, v_a_616_, v_snd_612_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_653_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_653_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_653_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_653_;
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
lean_ctor_set(v___x_625_, 1, v_snd_612_);
lean_ctor_set(v___x_625_, 0, v___x_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_snd_612_);
v___x_629_ = v_reuseFailAlloc_636_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v_snd_623_);
lean_ctor_set(v___x_614_, 0, v___x_629_);
v___x_631_ = v___x_614_;
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
lean_object* v_snd_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_651_; 
lean_del_object(v___x_620_);
lean_del_object(v___x_614_);
lean_dec(v_snd_612_);
v_snd_639_ = lean_ctor_get(v_a_618_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_a_618_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v_a_618_, 0);
lean_dec(v_unused_652_);
v___x_641_ = v_a_618_;
v_isShared_642_ = v_isSharedCheck_651_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_snd_639_);
lean_dec(v_a_618_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_651_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_a_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v_a_643_ = lean_ctor_get(v_fst_622_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v_fst_622_, 1);
v___x_644_ = lean_box(0);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v_a_643_);
lean_ctor_set(v___x_641_, 0, v___x_644_);
v___x_646_ = v___x_641_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_a_643_);
v___x_646_ = v_reuseFailAlloc_650_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
size_t v___x_647_; size_t v___x_648_; 
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_595_, v___x_647_);
v_i_595_ = v___x_648_;
v_b_596_ = v___x_646_;
v___y_597_ = v_snd_639_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_del_object(v___x_614_);
lean_dec(v_snd_612_);
v_a_654_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_617_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_617_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_664_ = _args[0];
lean_object* v_as_665_ = _args[1];
lean_object* v_sz_666_ = _args[2];
lean_object* v_i_667_ = _args[3];
lean_object* v_b_668_ = _args[4];
lean_object* v___y_669_ = _args[5];
lean_object* v___y_670_ = _args[6];
lean_object* v___y_671_ = _args[7];
lean_object* v___y_672_ = _args[8];
lean_object* v___y_673_ = _args[9];
lean_object* v___y_674_ = _args[10];
lean_object* v___y_675_ = _args[11];
lean_object* v___y_676_ = _args[12];
lean_object* v___y_677_ = _args[13];
lean_object* v___y_678_ = _args[14];
lean_object* v___y_679_ = _args[15];
lean_object* v___y_680_ = _args[16];
_start:
{
size_t v_sz_boxed_681_; size_t v_i_boxed_682_; lean_object* v_res_683_; 
v_sz_boxed_681_ = lean_unbox_usize(v_sz_666_);
lean_dec(v_sz_666_);
v_i_boxed_682_ = lean_unbox_usize(v_i_667_);
lean_dec(v_i_667_);
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_664_, v_as_665_, v_sz_boxed_681_, v_i_boxed_682_, v_b_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v_as_665_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0___boxed(lean_object* v_init_684_, lean_object* v_n_685_, lean_object* v_b_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_684_, v_n_685_, v_b_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v_n_685_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(lean_object* v_t_700_, lean_object* v_init_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_b_715_; lean_object* v___y_716_; lean_object* v_root_719_; lean_object* v_tail_720_; lean_object* v___x_721_; 
v_root_719_ = lean_ctor_get(v_t_700_, 0);
v_tail_720_ = lean_ctor_get(v_t_700_, 1);
v___x_721_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_701_, v_root_719_, v_init_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v_fst_723_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v_fst_723_ = lean_ctor_get(v_a_722_, 0);
lean_inc(v_fst_723_);
if (lean_obj_tag(v_fst_723_) == 0)
{
lean_object* v_snd_724_; lean_object* v_a_725_; 
v_snd_724_ = lean_ctor_get(v_a_722_, 1);
lean_inc(v_snd_724_);
lean_dec(v_a_722_);
v_a_725_ = lean_ctor_get(v_fst_723_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v_fst_723_, 1);
v_b_715_ = v_a_725_;
v___y_716_ = v_snd_724_;
goto v___jp_714_;
}
else
{
lean_object* v_snd_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_768_; 
v_snd_726_ = lean_ctor_get(v_a_722_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_a_722_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v_a_722_, 0);
lean_dec(v_unused_769_);
v___x_728_ = v_a_722_;
v_isShared_729_ = v_isSharedCheck_768_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_snd_726_);
lean_dec(v_a_722_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_768_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v_a_730_ = lean_ctor_get(v_fst_723_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v_fst_723_, 1);
v___x_731_ = lean_box(0);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v_a_730_);
lean_ctor_set(v___x_728_, 0, v___x_731_);
v___x_733_ = v___x_728_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_a_730_);
v___x_733_ = v_reuseFailAlloc_767_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
size_t v_sz_734_; size_t v___x_735_; lean_object* v___x_736_; 
v_sz_734_ = lean_array_size(v_tail_720_);
v___x_735_ = ((size_t)0ULL);
v___x_736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_tail_720_, v_sz_734_, v___x_735_, v___x_733_, v_snd_726_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_758_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_758_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_758_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_758_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_fst_741_; lean_object* v_fst_742_; 
v_fst_741_ = lean_ctor_get(v_a_737_, 0);
lean_inc(v_fst_741_);
v_fst_742_ = lean_ctor_get(v_fst_741_, 0);
if (lean_obj_tag(v_fst_742_) == 0)
{
lean_object* v_snd_743_; lean_object* v_snd_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_754_; 
v_snd_743_ = lean_ctor_get(v_a_737_, 1);
lean_inc(v_snd_743_);
lean_dec(v_a_737_);
v_snd_744_ = lean_ctor_get(v_fst_741_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_fst_741_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v_fst_741_, 0);
lean_dec(v_unused_755_);
v___x_746_ = v_fst_741_;
v_isShared_747_ = v_isSharedCheck_754_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snd_744_);
lean_dec(v_fst_741_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_754_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v_snd_743_);
lean_ctor_set(v___x_746_, 0, v_snd_744_);
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_snd_744_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_snd_743_);
v___x_749_ = v_reuseFailAlloc_753_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_749_);
v___x_751_ = v___x_739_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_snd_756_; lean_object* v_val_757_; 
lean_inc_ref(v_fst_742_);
lean_dec(v_fst_741_);
lean_del_object(v___x_739_);
v_snd_756_ = lean_ctor_get(v_a_737_, 1);
lean_inc(v_snd_756_);
lean_dec(v_a_737_);
v_val_757_ = lean_ctor_get(v_fst_742_, 0);
lean_inc(v_val_757_);
lean_dec_ref_known(v_fst_742_, 1);
v_b_715_ = v_val_757_;
v___y_716_ = v_snd_756_;
goto v___jp_714_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
v_a_759_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_736_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_736_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
v_a_770_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_721_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_721_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
v___jp_714_:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v_b_715_);
lean_ctor_set(v___x_717_, 1, v___y_716_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0___boxed(lean_object* v_t_778_, lean_object* v_init_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v_t_778_, v_init_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v_t_778_);
return v_res_792_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(lean_object* v_xs_793_, lean_object* v_i_794_){
_start:
{
lean_object* v_size_795_; uint8_t v___x_796_; 
v_size_795_ = lean_ctor_get(v_xs_793_, 2);
v___x_796_ = lean_nat_dec_lt(v_i_794_, v_size_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0___boxed(lean_object* v_xs_797_, lean_object* v_i_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_xs_797_, v_i_798_);
lean_dec(v_i_798_);
lean_dec_ref(v_xs_797_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(lean_object* v_a_802_, lean_object* v_range_803_, lean_object* v_b_804_, lean_object* v_i_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_stop_818_; lean_object* v_step_819_; uint8_t v___x_820_; 
v_stop_818_ = lean_ctor_get(v_range_803_, 1);
v_step_819_ = lean_ctor_get(v_range_803_, 2);
v___x_820_ = lean_nat_dec_lt(v_i_805_, v_stop_818_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v_i_805_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_b_804_);
lean_ctor_set(v___x_821_, 1, v___y_806_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_i_805_, v___y_807_, v___y_815_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_825_; lean_object* v_snd_827_; lean_object* v___y_831_; lean_object* v___y_832_; uint8_t v___x_839_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
v___x_825_ = lean_box(0);
v___x_839_ = lean_unbox(v_a_824_);
lean_dec(v_a_824_);
if (v___x_839_ == 0)
{
lean_object* v_dvds_840_; lean_object* v_lowers_841_; lean_object* v_uppers_842_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___x_854_; lean_object* v___y_856_; uint8_t v___x_863_; 
v_dvds_840_ = lean_ctor_get(v_a_802_, 6);
v_lowers_841_ = lean_ctor_get(v_a_802_, 7);
v_uppers_842_ = lean_ctor_get(v_a_802_, 8);
v___x_854_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0);
v___x_863_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_lowers_841_, v_i_805_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; 
v___x_864_ = l_outOfBounds___redArg(v___x_854_);
v___y_856_ = v___x_864_;
goto v___jp_855_;
}
else
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_PersistentArray_get_x21___redArg(v___x_854_, v_lowers_841_, v_i_805_);
v___y_856_ = v___x_865_;
goto v___jp_855_;
}
v___jp_843_:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_845_, v___x_825_, v___y_844_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec_ref(v___y_845_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v_snd_848_; lean_object* v_size_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v_snd_848_ = lean_ctor_get(v_a_847_, 1);
lean_inc(v_snd_848_);
lean_dec(v_a_847_);
v_size_849_ = lean_ctor_get(v_dvds_840_, 2);
v___x_850_ = lean_box(0);
v___x_851_ = lean_nat_dec_lt(v_i_805_, v_size_849_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; 
v___x_852_ = l_outOfBounds___redArg(v___x_850_);
v___y_831_ = v_snd_848_;
v___y_832_ = v___x_852_;
goto v___jp_830_;
}
else
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_PersistentArray_get_x21___redArg(v___x_850_, v_dvds_840_, v_i_805_);
v___y_831_ = v_snd_848_;
v___y_832_ = v___x_853_;
goto v___jp_830_;
}
}
else
{
lean_dec(v_i_805_);
return v___x_846_;
}
}
v___jp_855_:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_856_, v___x_825_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec_ref(v___y_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v_snd_859_; uint8_t v___x_860_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v_snd_859_ = lean_ctor_get(v_a_858_, 1);
lean_inc(v_snd_859_);
lean_dec(v_a_858_);
v___x_860_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_uppers_842_, v_i_805_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
v___x_861_ = l_outOfBounds___redArg(v___x_854_);
v___y_844_ = v_snd_859_;
v___y_845_ = v___x_861_;
goto v___jp_843_;
}
else
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentArray_get_x21___redArg(v___x_854_, v_uppers_842_, v_i_805_);
v___y_844_ = v_snd_859_;
v___y_845_ = v___x_862_;
goto v___jp_843_;
}
}
else
{
lean_dec(v_i_805_);
return v___x_857_;
}
}
}
else
{
v_snd_827_ = v___y_806_;
goto v___jp_826_;
}
v___jp_826_:
{
lean_object* v___x_828_; 
v___x_828_ = lean_nat_add(v_i_805_, v_step_819_);
lean_dec(v_i_805_);
v_b_804_ = v___x_825_;
v_i_805_ = v___x_828_;
v___y_806_ = v_snd_827_;
goto _start;
}
v___jp_830_:
{
if (lean_obj_tag(v___y_832_) == 1)
{
lean_object* v_val_833_; lean_object* v_d_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v_a_837_; lean_object* v_snd_838_; 
v_val_833_ = lean_ctor_get(v___y_832_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v___y_832_, 1);
v_d_834_ = lean_ctor_get(v_val_833_, 0);
lean_inc(v_d_834_);
lean_dec(v_val_833_);
v___x_835_ = lean_nat_abs(v_d_834_);
lean_dec(v_d_834_);
v___x_836_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v___x_835_, v_i_805_, v___y_831_);
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref(v___x_836_);
v_snd_838_ = lean_ctor_get(v_a_837_, 1);
lean_inc(v_snd_838_);
lean_dec(v_a_837_);
v_snd_827_ = v_snd_838_;
goto v___jp_826_;
}
else
{
lean_dec(v___y_832_);
v_snd_827_ = v___y_831_;
goto v___jp_826_;
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v___y_806_);
lean_dec(v_i_805_);
v_a_866_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_823_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_823_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___boxed(lean_object* v_a_874_, lean_object* v_range_875_, lean_object* v_b_876_, lean_object* v_i_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_874_, v_range_875_, v_b_876_, v_i_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v_range_875_);
lean_dec_ref(v_a_874_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_892_, v_a_900_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v_vars_905_; lean_object* v_size_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_903_, 1);
v_vars_905_ = lean_ctor_get(v_a_904_, 0);
v_size_906_ = lean_ctor_get(v_vars_905_, 2);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = lean_unsigned_to_nat(1u);
lean_inc(v_size_906_);
v___x_909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v_size_906_);
lean_ctor_set(v___x_909_, 2, v___x_908_);
v___x_910_ = lean_box(0);
v___x_911_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_904_, v___x_909_, v___x_910_, v___x_907_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
lean_dec_ref_known(v___x_909_, 3);
lean_dec(v_a_904_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_928_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_928_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_928_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_928_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_snd_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_926_; 
v_snd_916_ = lean_ctor_get(v_a_912_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_a_912_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_a_912_, 0);
lean_dec(v_unused_927_);
v___x_918_ = v_a_912_;
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_snd_916_);
lean_dec(v_a_912_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_910_);
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_snd_916_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_923_; 
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_921_);
v___x_923_ = v___x_914_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
else
{
return v___x_911_;
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec_ref(v_a_891_);
v_a_929_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_903_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_903_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go___boxed(lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec(v_a_938_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(lean_object* v_a_950_, lean_object* v_range_951_, lean_object* v_b_952_, lean_object* v_i_953_, lean_object* v_hs_954_, lean_object* v_hl_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_950_, v_range_951_, v_b_952_, v_i_953_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___boxed(lean_object** _args){
lean_object* v_a_969_ = _args[0];
lean_object* v_range_970_ = _args[1];
lean_object* v_b_971_ = _args[2];
lean_object* v_i_972_ = _args[3];
lean_object* v_hs_973_ = _args[4];
lean_object* v_hl_974_ = _args[5];
lean_object* v___y_975_ = _args[6];
lean_object* v___y_976_ = _args[7];
lean_object* v___y_977_ = _args[8];
lean_object* v___y_978_ = _args[9];
lean_object* v___y_979_ = _args[10];
lean_object* v___y_980_ = _args[11];
lean_object* v___y_981_ = _args[12];
lean_object* v___y_982_ = _args[13];
lean_object* v___y_983_ = _args[14];
lean_object* v___y_984_ = _args[15];
lean_object* v___y_985_ = _args[16];
lean_object* v___y_986_ = _args[17];
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(v_a_969_, v_range_970_, v_b_971_, v_i_972_, v_hs_973_, v_hl_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v_range_970_);
lean_dec_ref(v_a_969_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(lean_object* v_as_988_, size_t v_sz_989_, size_t v_i_990_, lean_object* v_b_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_988_, v_sz_989_, v_i_990_, v_b_991_, v___y_992_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1005_, lean_object* v_sz_1006_, lean_object* v_i_1007_, lean_object* v_b_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
size_t v_sz_boxed_1021_; size_t v_i_boxed_1022_; lean_object* v_res_1023_; 
v_sz_boxed_1021_ = lean_unbox_usize(v_sz_1006_);
lean_dec(v_sz_1006_);
v_i_boxed_1022_ = lean_unbox_usize(v_i_1007_);
lean_dec(v_i_1007_);
v_res_1023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(v_as_1005_, v_sz_boxed_1021_, v_i_boxed_1022_, v_b_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v_as_1005_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(lean_object* v_as_1024_, size_t v_sz_1025_, size_t v_i_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1024_, v_sz_1025_, v_i_1026_, v_b_1027_, v___y_1028_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_as_1041_, lean_object* v_sz_1042_, lean_object* v_i_1043_, lean_object* v_b_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
size_t v_sz_boxed_1057_; size_t v_i_boxed_1058_; lean_object* v_res_1059_; 
v_sz_boxed_1057_ = lean_unbox_usize(v_sz_1042_);
lean_dec(v_sz_1042_);
v_i_boxed_1058_ = lean_unbox_usize(v_i_1043_);
lean_dec(v_i_1043_);
v_res_1059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(v_as_1041_, v_sz_boxed_1057_, v_i_boxed_1058_, v_b_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v_as_1041_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1060_, v_a_1068_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v_vars_1073_; lean_object* v_size_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v_vars_1073_ = lean_ctor_get(v_a_1072_, 0);
lean_inc_ref(v_vars_1073_);
lean_dec(v_a_1072_);
v_size_1074_ = lean_ctor_get(v_vars_1073_, 2);
lean_inc(v_size_1074_);
lean_dec_ref(v_vars_1073_);
v___x_1075_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0));
v___x_1076_ = lean_mk_array(v_size_1074_, v___x_1075_);
v___x_1077_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v___x_1076_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1086_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v_snd_1082_; lean_object* v___x_1084_; 
v_snd_1082_ = lean_ctor_get(v_a_1078_, 1);
lean_inc(v_snd_1082_);
lean_dec(v_a_1078_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v_snd_1082_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_snd_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v_a_1087_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1077_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1077_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1071_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1071_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo___boxed(lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec(v_a_1103_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(lean_object* v_info_1115_){
_start:
{
lean_object* v_maxLowerCoeff_1116_; lean_object* v_maxUpperCoeff_1117_; lean_object* v_maxDvdCoeff_1118_; lean_object* v___y_1120_; uint8_t v___x_1122_; 
v_maxLowerCoeff_1116_ = lean_ctor_get(v_info_1115_, 0);
v_maxUpperCoeff_1117_ = lean_ctor_get(v_info_1115_, 1);
v_maxDvdCoeff_1118_ = lean_ctor_get(v_info_1115_, 2);
v___x_1122_ = lean_nat_dec_le(v_maxLowerCoeff_1116_, v_maxUpperCoeff_1117_);
if (v___x_1122_ == 0)
{
v___y_1120_ = v_maxUpperCoeff_1117_;
goto v___jp_1119_;
}
else
{
v___y_1120_ = v_maxLowerCoeff_1116_;
goto v___jp_1119_;
}
v___jp_1119_:
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_nat_dec_le(v_maxDvdCoeff_1118_, v___y_1120_);
if (v___x_1121_ == 0)
{
lean_inc(v_maxDvdCoeff_1118_);
return v_maxDvdCoeff_1118_;
}
else
{
lean_inc(v___y_1120_);
return v___y_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081___boxed(lean_object* v_info_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v_info_1123_);
lean_dec_ref(v_info_1123_);
return v_res_1124_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(lean_object* v_infos_1125_, lean_object* v_x_1126_, lean_object* v_y_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1128_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1129_ = lean_array_get_borrowed(v___x_1128_, v_infos_1125_, v_x_1126_);
v___x_1130_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1129_);
v___x_1131_ = lean_array_get_borrowed(v___x_1128_, v_infos_1125_, v_y_1127_);
v___x_1132_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_1131_);
v___x_1133_ = lean_nat_dec_lt(v___x_1130_, v___x_1132_);
if (v___x_1133_ == 0)
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_nat_dec_eq(v___x_1130_, v___x_1132_);
lean_dec(v___x_1132_);
lean_dec(v___x_1130_);
if (v___x_1134_ == 0)
{
uint8_t v___x_1135_; 
v___x_1135_ = 0;
return v___x_1135_;
}
else
{
uint8_t v___x_1136_; 
v___x_1136_ = 1;
return v___x_1136_;
}
}
else
{
uint8_t v___x_1137_; 
lean_dec(v___x_1132_);
lean_dec(v___x_1130_);
v___x_1137_ = 2;
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081___boxed(lean_object* v_infos_1138_, lean_object* v_x_1139_, lean_object* v_y_1140_){
_start:
{
uint8_t v_res_1141_; lean_object* v_r_1142_; 
v_res_1141_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1138_, v_x_1139_, v_y_1140_);
lean_dec(v_y_1140_);
lean_dec(v_x_1139_);
lean_dec_ref(v_infos_1138_);
v_r_1142_ = lean_box(v_res_1141_);
return v_r_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(lean_object* v_info_1143_){
_start:
{
lean_object* v_maxLowerCoeff_1144_; lean_object* v_maxUpperCoeff_1145_; lean_object* v_maxDvdCoeff_1146_; lean_object* v___y_1148_; uint8_t v___x_1150_; 
v_maxLowerCoeff_1144_ = lean_ctor_get(v_info_1143_, 0);
v_maxUpperCoeff_1145_ = lean_ctor_get(v_info_1143_, 1);
v_maxDvdCoeff_1146_ = lean_ctor_get(v_info_1143_, 2);
v___x_1150_ = lean_nat_dec_le(v_maxLowerCoeff_1144_, v_maxUpperCoeff_1145_);
if (v___x_1150_ == 0)
{
v___y_1148_ = v_maxLowerCoeff_1144_;
goto v___jp_1147_;
}
else
{
v___y_1148_ = v_maxUpperCoeff_1145_;
goto v___jp_1147_;
}
v___jp_1147_:
{
uint8_t v___x_1149_; 
v___x_1149_ = lean_nat_dec_le(v_maxDvdCoeff_1146_, v___y_1148_);
if (v___x_1149_ == 0)
{
lean_inc(v_maxDvdCoeff_1146_);
return v_maxDvdCoeff_1146_;
}
else
{
lean_inc(v___y_1148_);
return v___y_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082___boxed(lean_object* v_info_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v_info_1151_);
lean_dec_ref(v_info_1151_);
return v_res_1152_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(lean_object* v_infos_1153_, lean_object* v_x_1154_, lean_object* v_y_1155_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1156_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default));
v___x_1157_ = lean_array_get_borrowed(v___x_1156_, v_infos_1153_, v_x_1154_);
v___x_1158_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1157_);
v___x_1159_ = lean_array_get_borrowed(v___x_1156_, v_infos_1153_, v_y_1155_);
v___x_1160_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_1159_);
v___x_1161_ = lean_nat_dec_lt(v___x_1158_, v___x_1160_);
if (v___x_1161_ == 0)
{
uint8_t v___x_1162_; 
v___x_1162_ = lean_nat_dec_eq(v___x_1158_, v___x_1160_);
lean_dec(v___x_1160_);
lean_dec(v___x_1158_);
if (v___x_1162_ == 0)
{
uint8_t v___x_1163_; 
v___x_1163_ = 0;
return v___x_1163_;
}
else
{
uint8_t v___x_1164_; 
v___x_1164_ = 1;
return v___x_1164_;
}
}
else
{
uint8_t v___x_1165_; 
lean_dec(v___x_1160_);
lean_dec(v___x_1158_);
v___x_1165_ = 2;
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082___boxed(lean_object* v_infos_1166_, lean_object* v_x_1167_, lean_object* v_y_1168_){
_start:
{
uint8_t v_res_1169_; lean_object* v_r_1170_; 
v_res_1169_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1166_, v_x_1167_, v_y_1168_);
lean_dec(v_y_1168_);
lean_dec(v_x_1167_);
lean_dec_ref(v_infos_1166_);
v_r_1170_ = lean_box(v_res_1169_);
return v_r_1170_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(lean_object* v_infos_1171_, lean_object* v_x_1172_, lean_object* v_y_1173_){
_start:
{
uint8_t v___y_1175_; uint8_t v___x_1180_; 
v___x_1180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_1171_, v_x_1172_, v_y_1173_);
if (v___x_1180_ == 1)
{
uint8_t v___x_1181_; 
v___x_1181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_1171_, v_x_1172_, v_y_1173_);
v___y_1175_ = v___x_1181_;
goto v___jp_1174_;
}
else
{
v___y_1175_ = v___x_1180_;
goto v___jp_1174_;
}
v___jp_1174_:
{
if (v___y_1175_ == 1)
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_nat_dec_lt(v_x_1172_, v_y_1173_);
if (v___x_1176_ == 0)
{
uint8_t v___x_1177_; 
v___x_1177_ = lean_nat_dec_eq(v_x_1172_, v_y_1173_);
if (v___x_1177_ == 0)
{
uint8_t v___x_1178_; 
v___x_1178_ = 2;
return v___x_1178_;
}
else
{
return v___y_1175_;
}
}
else
{
uint8_t v___x_1179_; 
v___x_1179_ = 0;
return v___x_1179_;
}
}
else
{
return v___y_1175_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp___boxed(lean_object* v_infos_1182_, lean_object* v_x_1183_, lean_object* v_y_1184_){
_start:
{
uint8_t v_res_1185_; lean_object* v_r_1186_; 
v_res_1185_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_1182_, v_x_1183_, v_y_1184_);
lean_dec(v_y_1184_);
lean_dec(v_x_1183_);
lean_dec_ref(v_infos_1182_);
v_r_1186_ = lean_box(v_res_1185_);
return v_r_1186_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(lean_object* v_a_1187_, lean_object* v_x_1188_, lean_object* v_y_1189_){
_start:
{
uint8_t v___x_1190_; uint8_t v___x_1191_; uint8_t v___x_1192_; 
v___x_1190_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_a_1187_, v_x_1188_, v_y_1189_);
v___x_1191_ = 0;
v___x_1192_ = l_instDecidableEqOrdering(v___x_1190_, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0___boxed(lean_object* v_a_1193_, lean_object* v_x_1194_, lean_object* v_y_1195_){
_start:
{
uint8_t v_res_1196_; lean_object* v_r_1197_; 
v_res_1196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_a_1193_, v_x_1194_, v_y_1195_);
lean_dec(v_y_1195_);
lean_dec(v_x_1194_);
lean_dec_ref(v_a_1193_);
v_r_1197_ = lean_box(v_res_1196_);
return v_r_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(lean_object* v_a_1198_, lean_object* v_hi_1199_, lean_object* v_pivot_1200_, lean_object* v_as_1201_, lean_object* v_i_1202_, lean_object* v_k_1203_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_nat_dec_lt(v_k_1203_, v_hi_1199_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec(v_k_1203_);
v___x_1205_ = lean_array_fswap(v_as_1201_, v_i_1202_, v_hi_1199_);
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v_i_1202_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
return v___x_1206_;
}
else
{
lean_object* v___x_1207_; uint8_t v___x_1208_; uint8_t v___x_1209_; uint8_t v___x_1210_; 
v___x_1207_ = lean_array_fget_borrowed(v_as_1201_, v_k_1203_);
v___x_1208_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_a_1198_, v___x_1207_, v_pivot_1200_);
v___x_1209_ = 0;
v___x_1210_ = l_instDecidableEqOrdering(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = lean_nat_add(v_k_1203_, v___x_1211_);
lean_dec(v_k_1203_);
v_k_1203_ = v___x_1212_;
goto _start;
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1214_ = lean_array_fswap(v_as_1201_, v_i_1202_, v_k_1203_);
v___x_1215_ = lean_unsigned_to_nat(1u);
v___x_1216_ = lean_nat_add(v_i_1202_, v___x_1215_);
lean_dec(v_i_1202_);
v___x_1217_ = lean_nat_add(v_k_1203_, v___x_1215_);
lean_dec(v_k_1203_);
v_as_1201_ = v___x_1214_;
v_i_1202_ = v___x_1216_;
v_k_1203_ = v___x_1217_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_1219_, lean_object* v_hi_1220_, lean_object* v_pivot_1221_, lean_object* v_as_1222_, lean_object* v_i_1223_, lean_object* v_k_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_a_1219_, v_hi_1220_, v_pivot_1221_, v_as_1222_, v_i_1223_, v_k_1224_);
lean_dec(v_pivot_1221_);
lean_dec(v_hi_1220_);
lean_dec_ref(v_a_1219_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(lean_object* v_a_1226_, lean_object* v_n_1227_, lean_object* v_as_1228_, lean_object* v_lo_1229_, lean_object* v_hi_1230_){
_start:
{
lean_object* v___y_1232_; uint8_t v___x_1242_; 
v___x_1242_ = lean_nat_dec_lt(v_lo_1229_, v_hi_1230_);
if (v___x_1242_ == 0)
{
lean_dec(v_lo_1229_);
return v_as_1228_;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_mid_1245_; lean_object* v___y_1247_; lean_object* v___y_1253_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1243_ = lean_nat_add(v_lo_1229_, v_hi_1230_);
v___x_1244_ = lean_unsigned_to_nat(1u);
v_mid_1245_ = lean_nat_shiftr(v___x_1243_, v___x_1244_);
lean_dec(v___x_1243_);
v___x_1258_ = lean_array_fget_borrowed(v_as_1228_, v_mid_1245_);
v___x_1259_ = lean_array_fget_borrowed(v_as_1228_, v_lo_1229_);
v___x_1260_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_a_1226_, v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
v___y_1253_ = v_as_1228_;
goto v___jp_1252_;
}
else
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_array_fswap(v_as_1228_, v_lo_1229_, v_mid_1245_);
v___y_1253_ = v___x_1261_;
goto v___jp_1252_;
}
v___jp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1248_ = lean_array_fget_borrowed(v___y_1247_, v_mid_1245_);
v___x_1249_ = lean_array_fget_borrowed(v___y_1247_, v_hi_1230_);
v___x_1250_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_a_1226_, v___x_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_dec(v_mid_1245_);
v___y_1232_ = v___y_1247_;
goto v___jp_1231_;
}
else
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_array_fswap(v___y_1247_, v_mid_1245_, v_hi_1230_);
lean_dec(v_mid_1245_);
v___y_1232_ = v___x_1251_;
goto v___jp_1231_;
}
}
v___jp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1254_ = lean_array_fget_borrowed(v___y_1253_, v_hi_1230_);
v___x_1255_ = lean_array_fget_borrowed(v___y_1253_, v_lo_1229_);
v___x_1256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_a_1226_, v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
v___y_1247_ = v___y_1253_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_array_fswap(v___y_1253_, v_lo_1229_, v_hi_1230_);
v___y_1247_ = v___x_1257_;
goto v___jp_1246_;
}
}
}
v___jp_1231_:
{
lean_object* v_pivot_1233_; lean_object* v___x_1234_; lean_object* v_fst_1235_; lean_object* v_snd_1236_; uint8_t v___x_1237_; 
v_pivot_1233_ = lean_array_fget(v___y_1232_, v_hi_1230_);
lean_inc_n(v_lo_1229_, 2);
v___x_1234_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_a_1226_, v_hi_1230_, v_pivot_1233_, v___y_1232_, v_lo_1229_, v_lo_1229_);
lean_dec(v_pivot_1233_);
v_fst_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_fst_1235_);
v_snd_1236_ = lean_ctor_get(v___x_1234_, 1);
lean_inc(v_snd_1236_);
lean_dec_ref(v___x_1234_);
v___x_1237_ = lean_nat_dec_le(v_hi_1230_, v_fst_1235_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_1226_, v_n_1227_, v_snd_1236_, v_lo_1229_, v_fst_1235_);
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = lean_nat_add(v_fst_1235_, v___x_1239_);
lean_dec(v_fst_1235_);
v_as_1228_ = v___x_1238_;
v_lo_1229_ = v___x_1240_;
goto _start;
}
else
{
lean_dec(v_fst_1235_);
lean_dec(v_lo_1229_);
return v_snd_1236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___boxed(lean_object* v_a_1262_, lean_object* v_n_1263_, lean_object* v_as_1264_, lean_object* v_lo_1265_, lean_object* v_hi_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_1262_, v_n_1263_, v_as_1264_, v_lo_1265_, v_hi_1266_);
lean_dec(v_hi_1266_);
lean_dec(v_n_1263_);
lean_dec_ref(v_a_1262_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1320_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1320_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1320_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1268_, v_a_1276_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1311_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1311_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1311_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v_vars_1289_; lean_object* v_size_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_vars_1289_ = lean_ctor_get(v_a_1285_, 0);
lean_inc_ref(v_vars_1289_);
lean_dec(v_a_1285_);
v_size_1290_ = lean_ctor_get(v_vars_1289_, 2);
lean_inc(v_size_1290_);
lean_dec_ref(v_vars_1289_);
v___x_1291_ = l_Array_range(v_size_1290_);
v___x_1292_ = lean_array_get_size(v___x_1291_);
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_nat_dec_eq(v___x_1292_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___y_1305_; uint8_t v___x_1307_; 
lean_del_object(v___x_1282_);
v___x_1302_ = lean_unsigned_to_nat(1u);
v___x_1303_ = lean_nat_sub(v___x_1292_, v___x_1302_);
v___x_1307_ = lean_nat_dec_le(v___x_1300_, v___x_1303_);
if (v___x_1307_ == 0)
{
lean_inc(v___x_1303_);
v___y_1305_ = v___x_1303_;
goto v___jp_1304_;
}
else
{
v___y_1305_ = v___x_1300_;
goto v___jp_1304_;
}
v___jp_1304_:
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_nat_dec_le(v___y_1305_, v___x_1303_);
if (v___x_1306_ == 0)
{
lean_dec(v___x_1303_);
lean_inc(v___y_1305_);
v___y_1294_ = v___y_1305_;
v___y_1295_ = v___y_1305_;
goto v___jp_1293_;
}
else
{
v___y_1294_ = v___y_1305_;
v___y_1295_ = v___x_1303_;
goto v___jp_1293_;
}
}
}
else
{
lean_object* v___x_1309_; 
lean_del_object(v___x_1287_);
lean_dec(v_a_1280_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1291_);
v___x_1309_ = v___x_1282_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1291_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
v___jp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1296_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_1280_, v___x_1292_, v___x_1291_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec(v_a_1280_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1296_);
v___x_1298_ = v___x_1287_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_del_object(v___x_1282_);
lean_dec(v_a_1280_);
v_a_1312_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1284_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1284_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_a_1321_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1279_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1279_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___boxed(lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
lean_dec(v_a_1330_);
lean_dec(v_a_1329_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(lean_object* v_a_1341_, lean_object* v_n_1342_, lean_object* v_as_1343_, lean_object* v_lo_1344_, lean_object* v_hi_1345_, lean_object* v_w_1346_, lean_object* v_hlo_1347_, lean_object* v_hhi_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_1341_, v_n_1342_, v_as_1343_, v_lo_1344_, v_hi_1345_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___boxed(lean_object* v_a_1350_, lean_object* v_n_1351_, lean_object* v_as_1352_, lean_object* v_lo_1353_, lean_object* v_hi_1354_, lean_object* v_w_1355_, lean_object* v_hlo_1356_, lean_object* v_hhi_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(v_a_1350_, v_n_1351_, v_as_1352_, v_lo_1353_, v_hi_1354_, v_w_1355_, v_hlo_1356_, v_hhi_1357_);
lean_dec(v_hi_1354_);
lean_dec(v_n_1351_);
lean_dec_ref(v_a_1350_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(lean_object* v_a_1359_, lean_object* v_n_1360_, lean_object* v_lo_1361_, lean_object* v_hi_1362_, lean_object* v_hhi_1363_, lean_object* v_pivot_1364_, lean_object* v_as_1365_, lean_object* v_i_1366_, lean_object* v_k_1367_, lean_object* v_ilo_1368_, lean_object* v_ik_1369_, lean_object* v_w_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_a_1359_, v_hi_1362_, v_pivot_1364_, v_as_1365_, v_i_1366_, v_k_1367_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___boxed(lean_object* v_a_1372_, lean_object* v_n_1373_, lean_object* v_lo_1374_, lean_object* v_hi_1375_, lean_object* v_hhi_1376_, lean_object* v_pivot_1377_, lean_object* v_as_1378_, lean_object* v_i_1379_, lean_object* v_k_1380_, lean_object* v_ilo_1381_, lean_object* v_ik_1382_, lean_object* v_w_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(v_a_1372_, v_n_1373_, v_lo_1374_, v_hi_1375_, v_hhi_1376_, v_pivot_1377_, v_as_1378_, v_i_1379_, v_k_1380_, v_ilo_1381_, v_ik_1382_, v_w_1383_);
lean_dec(v_pivot_1377_);
lean_dec(v_hi_1375_);
lean_dec(v_lo_1374_);
lean_dec(v_n_1373_);
lean_dec_ref(v_a_1372_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(lean_object* v_perm_1385_, lean_object* v_range_1386_, lean_object* v_b_1387_, lean_object* v_i_1388_){
_start:
{
lean_object* v_stop_1389_; lean_object* v_step_1390_; uint8_t v___x_1391_; 
v_stop_1389_ = lean_ctor_get(v_range_1386_, 1);
v_step_1390_ = lean_ctor_get(v_range_1386_, 2);
v___x_1391_ = lean_nat_dec_lt(v_i_1388_, v_stop_1389_);
if (v___x_1391_ == 0)
{
lean_dec(v_i_1388_);
return v_b_1387_;
}
else
{
lean_object* v___x_1392_; lean_object* v_inv_1393_; lean_object* v___x_1394_; 
v___x_1392_ = lean_array_fget_borrowed(v_perm_1385_, v_i_1388_);
lean_inc(v_i_1388_);
v_inv_1393_ = lean_array_set(v_b_1387_, v___x_1392_, v_i_1388_);
v___x_1394_ = lean_nat_add(v_i_1388_, v_step_1390_);
lean_dec(v_i_1388_);
v_b_1387_ = v_inv_1393_;
v_i_1388_ = v___x_1394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg___boxed(lean_object* v_perm_1396_, lean_object* v_range_1397_, lean_object* v_b_1398_, lean_object* v_i_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1396_, v_range_1397_, v_b_1398_, v_i_1399_);
lean_dec_ref(v_range_1397_);
lean_dec_ref(v_perm_1396_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(lean_object* v_perm_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v_inv_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1402_ = lean_array_get_size(v_perm_1401_);
v___x_1403_ = lean_unsigned_to_nat(0u);
v_inv_1404_ = lean_mk_array(v___x_1402_, v___x_1403_);
v___x_1405_ = lean_unsigned_to_nat(1u);
v___x_1406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1403_);
lean_ctor_set(v___x_1406_, 1, v___x_1402_);
lean_ctor_set(v___x_1406_, 2, v___x_1405_);
v___x_1407_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1401_, v___x_1406_, v_inv_1404_, v___x_1403_);
lean_dec_ref_known(v___x_1406_, 3);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv___boxed(lean_object* v_perm_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_perm_1408_);
lean_dec_ref(v_perm_1408_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(lean_object* v_perm_1410_, lean_object* v_range_1411_, lean_object* v_b_1412_, lean_object* v_i_1413_, lean_object* v_hs_1414_, lean_object* v_hl_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_1410_, v_range_1411_, v_b_1412_, v_i_1413_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___boxed(lean_object* v_perm_1417_, lean_object* v_range_1418_, lean_object* v_b_1419_, lean_object* v_i_1420_, lean_object* v_hs_1421_, lean_object* v_hl_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(v_perm_1417_, v_range_1418_, v_b_1419_, v_i_1420_, v_hs_1421_, v_hl_1422_);
lean_dec_ref(v_range_1418_);
lean_dec_ref(v_perm_1417_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_reorder(lean_object* v_p_1424_, lean_object* v_old2new_1425_){
_start:
{
if (lean_obj_tag(v_p_1424_) == 0)
{
return v_p_1424_;
}
else
{
lean_object* v_k_1426_; lean_object* v_v_1427_; lean_object* v_p_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1438_; 
v_k_1426_ = lean_ctor_get(v_p_1424_, 0);
v_v_1427_ = lean_ctor_get(v_p_1424_, 1);
v_p_1428_ = lean_ctor_get(v_p_1424_, 2);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_p_1424_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1430_ = v_p_1424_;
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_p_1428_);
lean_inc(v_v_1427_);
lean_inc(v_k_1426_);
lean_dec(v_p_1424_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1432_ = lean_unsigned_to_nat(0u);
v___x_1433_ = lean_array_get_borrowed(v___x_1432_, v_old2new_1425_, v_v_1427_);
lean_dec(v_v_1427_);
v___x_1434_ = l_Int_Linear_Poly_reorder(v_p_1428_, v_old2new_1425_);
lean_inc(v___x_1433_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 2, v___x_1434_);
lean_ctor_set(v___x_1430_, 1, v___x_1433_);
v___x_1436_ = v___x_1430_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_k_1426_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_reorder___boxed(lean_object* v_p_1439_, lean_object* v_old2new_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Int_Linear_Poly_reorder(v_p_1439_, v_old2new_1440_);
lean_dec_ref(v_old2new_1440_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(lean_object* v_c_1442_, lean_object* v_old2new_1443_){
_start:
{
lean_object* v_d_1444_; lean_object* v_p_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_d_1444_ = lean_ctor_get(v_c_1442_, 0);
lean_inc(v_d_1444_);
v_p_1445_ = lean_ctor_get(v_c_1442_, 1);
lean_inc_ref(v_p_1445_);
v___x_1446_ = l_Int_Linear_Poly_reorder(v_p_1445_, v_old2new_1443_);
v___x_1447_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_c_1442_);
v___x_1448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1448_, 0, v_d_1444_);
lean_ctor_set(v___x_1448_, 1, v___x_1446_);
lean_ctor_set(v___x_1448_, 2, v___x_1447_);
v___x_1449_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder___boxed(lean_object* v_c_1450_, lean_object* v_old2new_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_c_1450_, v_old2new_1451_);
lean_dec_ref(v_old2new_1451_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(lean_object* v_c_1453_, lean_object* v_old2new_1454_){
_start:
{
lean_object* v_p_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_p_1455_ = lean_ctor_get(v_c_1453_, 0);
lean_inc_ref(v_p_1455_);
v___x_1456_ = l_Int_Linear_Poly_reorder(v_p_1455_, v_old2new_1454_);
v___x_1457_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_c_1453_);
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder___boxed(lean_object* v_c_1460_, lean_object* v_old2new_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_c_1460_, v_old2new_1461_);
lean_dec_ref(v_old2new_1461_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(lean_object* v_c_1463_, lean_object* v_old2new_1464_){
_start:
{
lean_object* v_p_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_p_1465_ = lean_ctor_get(v_c_1463_, 0);
lean_inc_ref(v_p_1465_);
v___x_1466_ = l_Int_Linear_Poly_reorder(v_p_1465_, v_old2new_1464_);
v___x_1467_ = lean_alloc_ctor(16, 1, 0);
lean_ctor_set(v___x_1467_, 0, v_c_1463_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder___boxed(lean_object* v_c_1470_, lean_object* v_old2new_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_c_1470_, v_old2new_1471_);
lean_dec_ref(v_old2new_1471_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(lean_object* v_c_1473_, lean_object* v_old2new_1474_){
_start:
{
lean_object* v_p_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v_p_1475_ = lean_ctor_get(v_c_1473_, 0);
lean_inc_ref(v_p_1475_);
v___x_1476_ = l_Int_Linear_Poly_reorder(v_p_1475_, v_old2new_1474_);
v___x_1477_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_c_1473_);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(v___x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder___boxed(lean_object* v_c_1480_, lean_object* v_old2new_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_c_1480_, v_old2new_1481_);
lean_dec_ref(v_old2new_1481_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(lean_object* v_new2old_1483_, lean_object* v_inst_1484_, lean_object* v_m_1485_, lean_object* v_i_1486_, lean_object* v_h_1487_, lean_object* v_____s_1488_){
_start:
{
lean_object* v_j_1489_; lean_object* v___x_1490_; lean_object* v_r_1491_; lean_object* v___x_1492_; 
v_j_1489_ = lean_array_fget_borrowed(v_new2old_1483_, v_i_1486_);
v___x_1490_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_1484_, v_m_1485_, v_j_1489_);
v_r_1491_ = l_Lean_PersistentArray_push___redArg(v_____s_1488_, v___x_1490_);
v___x_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1492_, 0, v_r_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed(lean_object* v_new2old_1493_, lean_object* v_inst_1494_, lean_object* v_m_1495_, lean_object* v_i_1496_, lean_object* v_h_1497_, lean_object* v_____s_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(v_new2old_1493_, v_inst_1494_, v_m_1495_, v_i_1496_, v_h_1497_, v_____s_1498_);
lean_dec(v_i_1496_);
lean_dec_ref(v_m_1495_);
lean_dec(v_inst_1494_);
lean_dec_ref(v_new2old_1493_);
return v_res_1499_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = lean_unsigned_to_nat(32u);
v___x_1520_ = lean_mk_empty_array_with_capacity(v___x_1519_);
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11(void){
_start:
{
size_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v_r_1527_; 
v___x_1522_ = ((size_t)5ULL);
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = lean_unsigned_to_nat(32u);
v___x_1525_ = lean_mk_empty_array_with_capacity(v___x_1524_);
v___x_1526_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10);
v_r_1527_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_r_1527_, 0, v___x_1526_);
lean_ctor_set(v_r_1527_, 1, v___x_1525_);
lean_ctor_set(v_r_1527_, 2, v___x_1523_);
lean_ctor_set(v_r_1527_, 3, v___x_1523_);
lean_ctor_set_usize(v_r_1527_, 4, v___x_1522_);
return v_r_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(lean_object* v_inst_1528_, lean_object* v_m_1529_, lean_object* v_new2old_1530_){
_start:
{
lean_object* v___f_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v_r_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_inc_ref(v_new2old_1530_);
v___f_1531_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1531_, 0, v_new2old_1530_);
lean_closure_set(v___f_1531_, 1, v_inst_1528_);
lean_closure_set(v___f_1531_, 2, v_m_1529_);
v___x_1532_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9));
v___x_1533_ = lean_unsigned_to_nat(0u);
v_r_1534_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11);
v___x_1535_ = lean_array_get_size(v_new2old_1530_);
lean_dec_ref(v_new2old_1530_);
v___x_1536_ = lean_unsigned_to_nat(1u);
v___x_1537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1533_);
lean_ctor_set(v___x_1537_, 1, v___x_1535_);
lean_ctor_set(v___x_1537_, 2, v___x_1536_);
v___x_1538_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), v___x_1532_, v___x_1537_, v___f_1531_, v_r_1534_, v___x_1533_, lean_box(0), lean_box(0));
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap(lean_object* v_00_u03b1_1539_, lean_object* v_inst_1540_, lean_object* v_m_1541_, lean_object* v_new2old_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v_inst_1540_, v_m_1541_, v_new2old_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_, lean_object* v_x_1547_){
_start:
{
lean_object* v_ks_1548_; lean_object* v_vs_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1573_; 
v_ks_1548_ = lean_ctor_get(v_x_1544_, 0);
v_vs_1549_ = lean_ctor_get(v_x_1544_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_x_1544_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1551_ = v_x_1544_;
v_isShared_1552_ = v_isSharedCheck_1573_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_vs_1549_);
lean_inc(v_ks_1548_);
lean_dec(v_x_1544_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1573_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = lean_array_get_size(v_ks_1548_);
v___x_1554_ = lean_nat_dec_lt(v_x_1545_, v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
lean_dec(v_x_1545_);
v___x_1555_ = lean_array_push(v_ks_1548_, v_x_1546_);
v___x_1556_ = lean_array_push(v_vs_1549_, v_x_1547_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 1, v___x_1556_);
lean_ctor_set(v___x_1551_, 0, v___x_1555_);
v___x_1558_ = v___x_1551_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
else
{
lean_object* v_k_x27_1560_; uint8_t v___x_1561_; 
v_k_x27_1560_ = lean_array_fget_borrowed(v_ks_1548_, v_x_1545_);
v___x_1561_ = l_Int_Linear_instBEqPoly_beq(v_x_1546_, v_k_x27_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1563_; 
if (v_isShared_1552_ == 0)
{
v___x_1563_ = v___x_1551_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_ks_1548_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_vs_1549_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = lean_nat_add(v_x_1545_, v___x_1564_);
lean_dec(v_x_1545_);
v_x_1544_ = v___x_1563_;
v_x_1545_ = v___x_1565_;
goto _start;
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1568_ = lean_array_fset(v_ks_1548_, v_x_1545_, v_x_1546_);
v___x_1569_ = lean_array_fset(v_vs_1549_, v_x_1545_, v_x_1547_);
lean_dec(v_x_1545_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 1, v___x_1569_);
lean_ctor_set(v___x_1551_, 0, v___x_1568_);
v___x_1571_ = v___x_1551_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1574_, lean_object* v_k_1575_, lean_object* v_v_1576_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_n_1574_, v___x_1577_, v_k_1575_, v_v_1576_);
return v___x_1578_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(lean_object* v_x_1580_, size_t v_x_1581_, size_t v_x_1582_, lean_object* v_x_1583_, lean_object* v_x_1584_){
_start:
{
if (lean_obj_tag(v_x_1580_) == 0)
{
lean_object* v_es_1585_; size_t v___x_1586_; size_t v___x_1587_; lean_object* v_j_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v_es_1585_ = lean_ctor_get(v_x_1580_, 0);
v___x_1586_ = ((size_t)31ULL);
v___x_1587_ = lean_usize_land(v_x_1581_, v___x_1586_);
v_j_1588_ = lean_usize_to_nat(v___x_1587_);
v___x_1589_ = lean_array_get_size(v_es_1585_);
v___x_1590_ = lean_nat_dec_lt(v_j_1588_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_dec(v_j_1588_);
lean_dec(v_x_1584_);
lean_dec_ref(v_x_1583_);
return v_x_1580_;
}
else
{
lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1629_; 
lean_inc_ref(v_es_1585_);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_x_1580_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; 
v_unused_1630_ = lean_ctor_get(v_x_1580_, 0);
lean_dec(v_unused_1630_);
v___x_1592_ = v_x_1580_;
v_isShared_1593_ = v_isSharedCheck_1629_;
goto v_resetjp_1591_;
}
else
{
lean_dec(v_x_1580_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1629_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_v_1594_; lean_object* v___x_1595_; lean_object* v_xs_x27_1596_; lean_object* v___y_1598_; 
v_v_1594_ = lean_array_fget(v_es_1585_, v_j_1588_);
v___x_1595_ = lean_box(0);
v_xs_x27_1596_ = lean_array_fset(v_es_1585_, v_j_1588_, v___x_1595_);
switch(lean_obj_tag(v_v_1594_))
{
case 0:
{
lean_object* v_key_1603_; lean_object* v_val_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1614_; 
v_key_1603_ = lean_ctor_get(v_v_1594_, 0);
v_val_1604_ = lean_ctor_get(v_v_1594_, 1);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_v_1594_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1606_ = v_v_1594_;
v_isShared_1607_ = v_isSharedCheck_1614_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_val_1604_);
lean_inc(v_key_1603_);
lean_dec(v_v_1594_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1614_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
uint8_t v___x_1608_; 
v___x_1608_ = l_Int_Linear_instBEqPoly_beq(v_x_1583_, v_key_1603_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_del_object(v___x_1606_);
v___x_1609_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1603_, v_val_1604_, v_x_1583_, v_x_1584_);
v___x_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
v___y_1598_ = v___x_1610_;
goto v___jp_1597_;
}
else
{
lean_object* v___x_1612_; 
lean_dec(v_val_1604_);
lean_dec(v_key_1603_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 1, v_x_1584_);
lean_ctor_set(v___x_1606_, 0, v_x_1583_);
v___x_1612_ = v___x_1606_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_x_1583_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_x_1584_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
v___y_1598_ = v___x_1612_;
goto v___jp_1597_;
}
}
}
}
case 1:
{
lean_object* v_node_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1627_; 
v_node_1615_ = lean_ctor_get(v_v_1594_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_v_1594_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1617_ = v_v_1594_;
v_isShared_1618_ = v_isSharedCheck_1627_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_node_1615_);
lean_dec(v_v_1594_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1627_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
size_t v___x_1619_; size_t v___x_1620_; size_t v___x_1621_; size_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1619_ = ((size_t)5ULL);
v___x_1620_ = lean_usize_shift_right(v_x_1581_, v___x_1619_);
v___x_1621_ = ((size_t)1ULL);
v___x_1622_ = lean_usize_add(v_x_1582_, v___x_1621_);
v___x_1623_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_node_1615_, v___x_1620_, v___x_1622_, v_x_1583_, v_x_1584_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1623_);
v___x_1625_ = v___x_1617_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
v___y_1598_ = v___x_1625_;
goto v___jp_1597_;
}
}
}
default: 
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1628_, 0, v_x_1583_);
lean_ctor_set(v___x_1628_, 1, v_x_1584_);
v___y_1598_ = v___x_1628_;
goto v___jp_1597_;
}
}
v___jp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1599_ = lean_array_fset(v_xs_x27_1596_, v_j_1588_, v___y_1598_);
lean_dec(v_j_1588_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1599_);
v___x_1601_ = v___x_1592_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v_ks_1631_; lean_object* v_vs_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1652_; 
v_ks_1631_ = lean_ctor_get(v_x_1580_, 0);
v_vs_1632_ = lean_ctor_get(v_x_1580_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_x_1580_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1634_ = v_x_1580_;
v_isShared_1635_ = v_isSharedCheck_1652_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_vs_1632_);
lean_inc(v_ks_1631_);
lean_dec(v_x_1580_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1652_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_ks_1631_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_vs_1632_);
v___x_1637_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v_newNode_1638_; uint8_t v___y_1640_; size_t v___x_1646_; uint8_t v___x_1647_; 
v_newNode_1638_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v___x_1637_, v_x_1583_, v_x_1584_);
v___x_1646_ = ((size_t)7ULL);
v___x_1647_ = lean_usize_dec_le(v___x_1646_, v_x_1582_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1648_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1638_);
v___x_1649_ = lean_unsigned_to_nat(4u);
v___x_1650_ = lean_nat_dec_lt(v___x_1648_, v___x_1649_);
lean_dec(v___x_1648_);
v___y_1640_ = v___x_1650_;
goto v___jp_1639_;
}
else
{
v___y_1640_ = v___x_1647_;
goto v___jp_1639_;
}
v___jp_1639_:
{
if (v___y_1640_ == 0)
{
lean_object* v_ks_1641_; lean_object* v_vs_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_ks_1641_ = lean_ctor_get(v_newNode_1638_, 0);
lean_inc_ref(v_ks_1641_);
v_vs_1642_ = lean_ctor_get(v_newNode_1638_, 1);
lean_inc_ref(v_vs_1642_);
lean_dec_ref(v_newNode_1638_);
v___x_1643_ = lean_unsigned_to_nat(0u);
v___x_1644_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0);
v___x_1645_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_x_1582_, v_ks_1641_, v_vs_1642_, v___x_1643_, v___x_1644_);
lean_dec_ref(v_vs_1642_);
lean_dec_ref(v_ks_1641_);
return v___x_1645_;
}
else
{
return v_newNode_1638_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(size_t v_depth_1653_, lean_object* v_keys_1654_, lean_object* v_vals_1655_, lean_object* v_i_1656_, lean_object* v_entries_1657_){
_start:
{
lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1658_ = lean_array_get_size(v_keys_1654_);
v___x_1659_ = lean_nat_dec_lt(v_i_1656_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_dec(v_i_1656_);
return v_entries_1657_;
}
else
{
lean_object* v_k_1660_; lean_object* v_v_1661_; uint64_t v___x_1662_; size_t v_h_1663_; size_t v___x_1664_; lean_object* v___x_1665_; size_t v___x_1666_; size_t v___x_1667_; size_t v___x_1668_; size_t v_h_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_k_1660_ = lean_array_fget_borrowed(v_keys_1654_, v_i_1656_);
v_v_1661_ = lean_array_fget_borrowed(v_vals_1655_, v_i_1656_);
v___x_1662_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_k_1660_);
v_h_1663_ = lean_uint64_to_usize(v___x_1662_);
v___x_1664_ = ((size_t)5ULL);
v___x_1665_ = lean_unsigned_to_nat(1u);
v___x_1666_ = ((size_t)1ULL);
v___x_1667_ = lean_usize_sub(v_depth_1653_, v___x_1666_);
v___x_1668_ = lean_usize_mul(v___x_1664_, v___x_1667_);
v_h_1669_ = lean_usize_shift_right(v_h_1663_, v___x_1668_);
v___x_1670_ = lean_nat_add(v_i_1656_, v___x_1665_);
lean_dec(v_i_1656_);
lean_inc(v_v_1661_);
lean_inc(v_k_1660_);
v___x_1671_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_entries_1657_, v_h_1669_, v_depth_1653_, v_k_1660_, v_v_1661_);
v_i_1656_ = v___x_1670_;
v_entries_1657_ = v___x_1671_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1673_, lean_object* v_keys_1674_, lean_object* v_vals_1675_, lean_object* v_i_1676_, lean_object* v_entries_1677_){
_start:
{
size_t v_depth_boxed_1678_; lean_object* v_res_1679_; 
v_depth_boxed_1678_ = lean_unbox_usize(v_depth_1673_);
lean_dec(v_depth_1673_);
v_res_1679_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1678_, v_keys_1674_, v_vals_1675_, v_i_1676_, v_entries_1677_);
lean_dec_ref(v_vals_1675_);
lean_dec_ref(v_keys_1674_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___boxed(lean_object* v_x_1680_, lean_object* v_x_1681_, lean_object* v_x_1682_, lean_object* v_x_1683_, lean_object* v_x_1684_){
_start:
{
size_t v_x_1880__boxed_1685_; size_t v_x_1881__boxed_1686_; lean_object* v_res_1687_; 
v_x_1880__boxed_1685_ = lean_unbox_usize(v_x_1681_);
lean_dec(v_x_1681_);
v_x_1881__boxed_1686_ = lean_unbox_usize(v_x_1682_);
lean_dec(v_x_1682_);
v_res_1687_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1680_, v_x_1880__boxed_1685_, v_x_1881__boxed_1686_, v_x_1683_, v_x_1684_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(lean_object* v_x_1688_, lean_object* v_x_1689_, lean_object* v_x_1690_){
_start:
{
uint64_t v___x_1691_; size_t v___x_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
v___x_1691_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_1689_);
v___x_1692_ = lean_uint64_to_usize(v___x_1691_);
v___x_1693_ = ((size_t)1ULL);
v___x_1694_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1688_, v___x_1692_, v___x_1693_, v_x_1689_, v_x_1690_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(lean_object* v_old2new_1695_, lean_object* v_x_1696_, lean_object* v_____s_1697_){
_start:
{
lean_object* v_fst_1698_; lean_object* v_snd_1699_; lean_object* v___x_1700_; lean_object* v_m_x27_1701_; lean_object* v___x_1702_; 
v_fst_1698_ = lean_ctor_get(v_x_1696_, 0);
lean_inc(v_fst_1698_);
v_snd_1699_ = lean_ctor_get(v_x_1696_, 1);
lean_inc(v_snd_1699_);
lean_dec_ref(v_x_1696_);
v___x_1700_ = l_Int_Linear_Poly_reorder(v_fst_1698_, v_old2new_1695_);
v_m_x27_1701_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_____s_1697_, v___x_1700_, v_snd_1699_);
v___x_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1702_, 0, v_m_x27_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed(lean_object* v_old2new_1703_, lean_object* v_x_1704_, lean_object* v_____s_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(v_old2new_1703_, v_x_1704_, v_____s_1705_);
lean_dec_ref(v_old2new_1703_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_f_1707_, lean_object* v_keys_1708_, lean_object* v_vals_1709_, lean_object* v_i_1710_, lean_object* v_acc_1711_){
_start:
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = lean_array_get_size(v_keys_1708_);
v___x_1713_ = lean_nat_dec_lt(v_i_1710_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; 
lean_dec(v_i_1710_);
lean_dec_ref(v_f_1707_);
v___x_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1714_, 0, v_acc_1711_);
return v___x_1714_;
}
else
{
lean_object* v_k_1715_; lean_object* v_v_1716_; lean_object* v___x_1717_; 
v_k_1715_ = lean_array_fget_borrowed(v_keys_1708_, v_i_1710_);
v_v_1716_ = lean_array_fget_borrowed(v_vals_1709_, v_i_1710_);
lean_inc_ref(v_f_1707_);
lean_inc(v_v_1716_);
lean_inc(v_k_1715_);
v___x_1717_ = lean_apply_3(v_f_1707_, v_acc_1711_, v_k_1715_, v_v_1716_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_dec(v_i_1710_);
lean_dec_ref(v_f_1707_);
return v___x_1717_;
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v___x_1719_ = lean_unsigned_to_nat(1u);
v___x_1720_ = lean_nat_add(v_i_1710_, v___x_1719_);
lean_dec(v_i_1710_);
v_i_1710_ = v___x_1720_;
v_acc_1711_ = v_a_1718_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_f_1722_, lean_object* v_keys_1723_, lean_object* v_vals_1724_, lean_object* v_i_1725_, lean_object* v_acc_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1722_, v_keys_1723_, v_vals_1724_, v_i_1725_, v_acc_1726_);
lean_dec_ref(v_vals_1724_);
lean_dec_ref(v_keys_1723_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(lean_object* v_f_1728_, lean_object* v_x_1729_, lean_object* v_x_1730_){
_start:
{
if (lean_obj_tag(v_x_1729_) == 0)
{
lean_object* v_es_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1751_; 
v_es_1731_ = lean_ctor_get(v_x_1729_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_x_1729_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1733_ = v_x_1729_;
v_isShared_1734_ = v_isSharedCheck_1751_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_es_1731_);
lean_dec(v_x_1729_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1751_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1735_ = lean_unsigned_to_nat(0u);
v___x_1736_ = lean_array_get_size(v_es_1731_);
v___x_1737_ = lean_nat_dec_lt(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1739_; 
lean_dec_ref(v_es_1731_);
lean_dec_ref(v_f_1728_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set_tag(v___x_1733_, 1);
lean_ctor_set(v___x_1733_, 0, v_x_1730_);
v___x_1739_ = v___x_1733_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_x_1730_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
else
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_nat_dec_le(v___x_1736_, v___x_1736_);
if (v___x_1741_ == 0)
{
if (v___x_1737_ == 0)
{
lean_object* v___x_1743_; 
lean_dec_ref(v_es_1731_);
lean_dec_ref(v_f_1728_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set_tag(v___x_1733_, 1);
lean_ctor_set(v___x_1733_, 0, v_x_1730_);
v___x_1743_ = v___x_1733_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_x_1730_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
else
{
size_t v___x_1745_; size_t v___x_1746_; lean_object* v___x_1747_; 
lean_del_object(v___x_1733_);
v___x_1745_ = ((size_t)0ULL);
v___x_1746_ = lean_usize_of_nat(v___x_1736_);
v___x_1747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1728_, v_es_1731_, v___x_1745_, v___x_1746_, v_x_1730_);
lean_dec_ref(v_es_1731_);
return v___x_1747_;
}
}
else
{
size_t v___x_1748_; size_t v___x_1749_; lean_object* v___x_1750_; 
lean_del_object(v___x_1733_);
v___x_1748_ = ((size_t)0ULL);
v___x_1749_ = lean_usize_of_nat(v___x_1736_);
v___x_1750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1728_, v_es_1731_, v___x_1748_, v___x_1749_, v_x_1730_);
lean_dec_ref(v_es_1731_);
return v___x_1750_;
}
}
}
}
else
{
lean_object* v_ks_1752_; lean_object* v_vs_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_ks_1752_ = lean_ctor_get(v_x_1729_, 0);
lean_inc_ref(v_ks_1752_);
v_vs_1753_ = lean_ctor_get(v_x_1729_, 1);
lean_inc_ref(v_vs_1753_);
lean_dec_ref_known(v_x_1729_, 2);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1728_, v_ks_1752_, v_vs_1753_, v___x_1754_, v_x_1730_);
lean_dec_ref(v_vs_1753_);
lean_dec_ref(v_ks_1752_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(lean_object* v_f_1756_, lean_object* v_as_1757_, size_t v_i_1758_, size_t v_stop_1759_, lean_object* v_b_1760_){
_start:
{
lean_object* v_a_1762_; lean_object* v___y_1767_; uint8_t v___x_1769_; 
v___x_1769_ = lean_usize_dec_eq(v_i_1758_, v_stop_1759_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_array_uget_borrowed(v_as_1757_, v_i_1758_);
switch(lean_obj_tag(v___x_1770_))
{
case 0:
{
lean_object* v_key_1771_; lean_object* v_val_1772_; lean_object* v___x_1773_; 
v_key_1771_ = lean_ctor_get(v___x_1770_, 0);
v_val_1772_ = lean_ctor_get(v___x_1770_, 1);
lean_inc_ref(v_f_1756_);
lean_inc(v_val_1772_);
lean_inc(v_key_1771_);
v___x_1773_ = lean_apply_3(v_f_1756_, v_b_1760_, v_key_1771_, v_val_1772_);
v___y_1767_ = v___x_1773_;
goto v___jp_1766_;
}
case 1:
{
lean_object* v_node_1774_; lean_object* v___x_1775_; 
v_node_1774_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_node_1774_);
lean_inc_ref(v_f_1756_);
v___x_1775_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1756_, v_node_1774_, v_b_1760_);
v___y_1767_ = v___x_1775_;
goto v___jp_1766_;
}
default: 
{
v_a_1762_ = v_b_1760_;
goto v___jp_1761_;
}
}
}
else
{
lean_object* v___x_1776_; 
lean_dec_ref(v_f_1756_);
v___x_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1776_, 0, v_b_1760_);
return v___x_1776_;
}
v___jp_1761_:
{
size_t v___x_1763_; size_t v___x_1764_; 
v___x_1763_ = ((size_t)1ULL);
v___x_1764_ = lean_usize_add(v_i_1758_, v___x_1763_);
v_i_1758_ = v___x_1764_;
v_b_1760_ = v_a_1762_;
goto _start;
}
v___jp_1766_:
{
if (lean_obj_tag(v___y_1767_) == 0)
{
lean_dec_ref(v_f_1756_);
return v___y_1767_;
}
else
{
lean_object* v_a_1768_; 
v_a_1768_ = lean_ctor_get(v___y_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v___y_1767_, 1);
v_a_1762_ = v_a_1768_;
goto v___jp_1761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_f_1777_, lean_object* v_as_1778_, lean_object* v_i_1779_, lean_object* v_stop_1780_, lean_object* v_b_1781_){
_start:
{
size_t v_i_boxed_1782_; size_t v_stop_boxed_1783_; lean_object* v_res_1784_; 
v_i_boxed_1782_ = lean_unbox_usize(v_i_1779_);
lean_dec(v_i_1779_);
v_stop_boxed_1783_ = lean_unbox_usize(v_stop_1780_);
lean_dec(v_stop_1780_);
v_res_1784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1777_, v_as_1778_, v_i_boxed_1782_, v_stop_boxed_1783_, v_b_1781_);
lean_dec_ref(v_as_1778_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0(lean_object* v_f_1785_, lean_object* v_s_1786_, lean_object* v_a_1787_, lean_object* v_b_1788_){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_a_1787_);
lean_ctor_set(v___x_1789_, 1, v_b_1788_);
v___x_1790_ = lean_apply_2(v_f_1785_, v___x_1789_, v_s_1786_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
v_a_1799_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1790_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1790_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(lean_object* v_map_1807_, lean_object* v_init_1808_, lean_object* v_f_1809_){
_start:
{
lean_object* v___f_1810_; lean_object* v___x_1811_; lean_object* v_a_1812_; 
v___f_1810_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1810_, 0, v_f_1809_);
lean_inc_ref(v_map_1807_);
v___x_1811_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v___f_1810_, v_map_1807_, v_init_1808_);
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref(v___x_1811_);
return v_a_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___boxed(lean_object* v_map_1813_, lean_object* v_init_1814_, lean_object* v_f_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_1813_, v_init_1814_, v_f_1815_);
lean_dec_ref(v_map_1813_);
return v_res_1816_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0(void){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1817_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1(void){
_start:
{
lean_object* v___x_1818_; lean_object* v_m_x27_1819_; 
v___x_1818_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0);
v_m_x27_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_m_x27_1819_, 0, v___x_1818_);
return v_m_x27_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(lean_object* v_m_1820_, lean_object* v_old2new_1821_){
_start:
{
lean_object* v___f_1822_; lean_object* v_m_x27_1823_; lean_object* v___x_1824_; 
v___f_1822_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1822_, 0, v_old2new_1821_);
v_m_x27_1823_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
v___x_1824_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_m_1820_, v_m_x27_1823_, v___f_1822_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___boxed(lean_object* v_m_1825_, lean_object* v_old2new_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(v_m_1825_, v_old2new_1826_);
lean_dec_ref(v_m_1825_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0(lean_object* v_00_u03b2_1828_, lean_object* v_x_1829_, lean_object* v_x_1830_, lean_object* v_x_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_x_1829_, v_x_1830_, v_x_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(lean_object* v_00_u03c3_1833_, lean_object* v_00_u03b2_1834_, lean_object* v_map_1835_, lean_object* v_init_1836_, lean_object* v_f_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_1835_, v_init_1836_, v_f_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___boxed(lean_object* v_00_u03c3_1839_, lean_object* v_00_u03b2_1840_, lean_object* v_map_1841_, lean_object* v_init_1842_, lean_object* v_f_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(v_00_u03c3_1839_, v_00_u03b2_1840_, v_map_1841_, v_init_1842_, v_f_1843_);
lean_dec_ref(v_map_1841_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(lean_object* v_00_u03b2_1845_, lean_object* v_x_1846_, size_t v_x_1847_, size_t v_x_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_1846_, v_x_1847_, v_x_1848_, v_x_1849_, v_x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1852_, lean_object* v_x_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
size_t v_x_2231__boxed_1858_; size_t v_x_2232__boxed_1859_; lean_object* v_res_1860_; 
v_x_2231__boxed_1858_ = lean_unbox_usize(v_x_1854_);
lean_dec(v_x_1854_);
v_x_2232__boxed_1859_ = lean_unbox_usize(v_x_1855_);
lean_dec(v_x_1855_);
v_res_1860_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(v_00_u03b2_1852_, v_x_1853_, v_x_2231__boxed_1858_, v_x_2232__boxed_1859_, v_x_1856_, v_x_1857_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2___redArg(lean_object* v_map_1861_, lean_object* v_f_1862_, lean_object* v_init_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1862_, v_map_1861_, v_init_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2(lean_object* v_00_u03c3_1865_, lean_object* v_00_u03c3_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_map_1868_, lean_object* v_f_1869_, lean_object* v_init_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1869_, v_map_1868_, v_init_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1872_, lean_object* v_n_1873_, lean_object* v_k_1874_, lean_object* v_v_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v_n_1873_, v_k_1874_, v_v_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1877_, size_t v_depth_1878_, lean_object* v_keys_1879_, lean_object* v_vals_1880_, lean_object* v_heq_1881_, lean_object* v_i_1882_, lean_object* v_entries_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_1878_, v_keys_1879_, v_vals_1880_, v_i_1882_, v_entries_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1885_, lean_object* v_depth_1886_, lean_object* v_keys_1887_, lean_object* v_vals_1888_, lean_object* v_heq_1889_, lean_object* v_i_1890_, lean_object* v_entries_1891_){
_start:
{
size_t v_depth_boxed_1892_; lean_object* v_res_1893_; 
v_depth_boxed_1892_ = lean_unbox_usize(v_depth_1886_);
lean_dec(v_depth_1886_);
v_res_1893_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(v_00_u03b2_1885_, v_depth_boxed_1892_, v_keys_1887_, v_vals_1888_, v_heq_1889_, v_i_1890_, v_entries_1891_);
lean_dec_ref(v_vals_1888_);
lean_dec_ref(v_keys_1887_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5(lean_object* v_00_u03c3_1894_, lean_object* v_00_u03c3_1895_, lean_object* v_00_u03b1_1896_, lean_object* v_00_u03b2_1897_, lean_object* v_f_1898_, lean_object* v_x_1899_, lean_object* v_x_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_1898_, v_x_1899_, v_x_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1902_, lean_object* v_x_1903_, lean_object* v_x_1904_, lean_object* v_x_1905_, lean_object* v_x_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1903_, v_x_1904_, v_x_1905_, v_x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(lean_object* v_00_u03b1_1908_, lean_object* v_00_u03b2_1909_, lean_object* v_00_u03c3_1910_, lean_object* v_00_u03c3_1911_, lean_object* v_f_1912_, lean_object* v_as_1913_, size_t v_i_1914_, size_t v_stop_1915_, lean_object* v_b_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_1912_, v_as_1913_, v_i_1914_, v_stop_1915_, v_b_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1918_, lean_object* v_00_u03b2_1919_, lean_object* v_00_u03c3_1920_, lean_object* v_00_u03c3_1921_, lean_object* v_f_1922_, lean_object* v_as_1923_, lean_object* v_i_1924_, lean_object* v_stop_1925_, lean_object* v_b_1926_){
_start:
{
size_t v_i_boxed_1927_; size_t v_stop_boxed_1928_; lean_object* v_res_1929_; 
v_i_boxed_1927_ = lean_unbox_usize(v_i_1924_);
lean_dec(v_i_1924_);
v_stop_boxed_1928_ = lean_unbox_usize(v_stop_1925_);
lean_dec(v_stop_1925_);
v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_1918_, v_00_u03b2_1919_, v_00_u03c3_1920_, v_00_u03c3_1921_, v_f_1922_, v_as_1923_, v_i_boxed_1927_, v_stop_boxed_1928_, v_b_1926_);
lean_dec_ref(v_as_1923_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03c3_1930_, lean_object* v_00_u03c3_1931_, lean_object* v_00_u03b1_1932_, lean_object* v_00_u03b2_1933_, lean_object* v_f_1934_, lean_object* v_keys_1935_, lean_object* v_vals_1936_, lean_object* v_heq_1937_, lean_object* v_i_1938_, lean_object* v_acc_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_1934_, v_keys_1935_, v_vals_1936_, v_i_1938_, v_acc_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03c3_1941_, lean_object* v_00_u03c3_1942_, lean_object* v_00_u03b1_1943_, lean_object* v_00_u03b2_1944_, lean_object* v_f_1945_, lean_object* v_keys_1946_, lean_object* v_vals_1947_, lean_object* v_heq_1948_, lean_object* v_i_1949_, lean_object* v_acc_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(v_00_u03c3_1941_, v_00_u03c3_1942_, v_00_u03b1_1943_, v_00_u03b2_1944_, v_f_1945_, v_keys_1946_, v_vals_1947_, v_heq_1948_, v_i_1949_, v_acc_1950_);
lean_dec_ref(v_vals_1947_);
lean_dec_ref(v_keys_1946_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(lean_object* v___x_1952_, lean_object* v_x_1953_){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = lean_unsigned_to_nat(0u);
v___x_1955_ = lean_array_get_borrowed(v___x_1954_, v___x_1952_, v_x_1953_);
lean_inc(v___x_1955_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(lean_object* v___x_1956_, lean_object* v_x_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(v___x_1956_, v_x_1957_);
lean_dec(v_x_1957_);
lean_dec_ref(v___x_1956_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0(lean_object* v_f_1959_, lean_object* v_x_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_apply_1(v_f_1959_, v_x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(lean_object* v_f_1962_, lean_object* v_as_1963_, lean_object* v_i_1964_, lean_object* v_acc_1965_){
_start:
{
lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1966_ = lean_array_get_size(v_as_1963_);
v___x_1967_ = lean_nat_dec_eq(v_i_1964_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1968_ = lean_array_fget_borrowed(v_as_1963_, v_i_1964_);
lean_inc(v_f_1962_);
lean_inc(v___x_1968_);
v___x_1969_ = lean_apply_1(v_f_1962_, v___x_1968_);
v___x_1970_ = lean_unsigned_to_nat(1u);
v___x_1971_ = lean_nat_add(v_i_1964_, v___x_1970_);
lean_dec(v_i_1964_);
v___x_1972_ = lean_array_push(v_acc_1965_, v___x_1969_);
v_i_1964_ = v___x_1971_;
v_acc_1965_ = v___x_1972_;
goto _start;
}
else
{
lean_dec(v_i_1964_);
lean_dec(v_f_1962_);
return v_acc_1965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg___boxed(lean_object* v_f_1974_, lean_object* v_as_1975_, lean_object* v_i_1976_, lean_object* v_acc_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(v_f_1974_, v_as_1975_, v_i_1976_, v_acc_1977_);
lean_dec_ref(v_as_1975_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(lean_object* v_f_1979_, lean_object* v_as_1980_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = lean_array_get_size(v_as_1980_);
v___x_1983_ = lean_mk_empty_array_with_capacity(v___x_1982_);
v___x_1984_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(v_f_1979_, v_as_1980_, v___x_1981_, v___x_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg___boxed(lean_object* v_f_1985_, lean_object* v_as_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(v_f_1985_, v_as_1986_);
lean_dec_ref(v_as_1986_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(lean_object* v_f_1988_, size_t v_sz_1989_, size_t v_i_1990_, lean_object* v_bs_1991_){
_start:
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_usize_dec_lt(v_i_1990_, v_sz_1989_);
if (v___x_1992_ == 0)
{
lean_dec(v_f_1988_);
return v_bs_1991_;
}
else
{
lean_object* v_v_1993_; lean_object* v___x_1994_; lean_object* v_bs_x27_1995_; lean_object* v___y_1997_; 
v_v_1993_ = lean_array_uget(v_bs_1991_, v_i_1990_);
v___x_1994_ = lean_unsigned_to_nat(0u);
v_bs_x27_1995_ = lean_array_uset(v_bs_1991_, v_i_1990_, v___x_1994_);
switch(lean_obj_tag(v_v_1993_))
{
case 0:
{
lean_object* v_key_2002_; lean_object* v_val_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2011_; 
v_key_2002_ = lean_ctor_get(v_v_1993_, 0);
v_val_2003_ = lean_ctor_get(v_v_1993_, 1);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_v_1993_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2005_ = v_v_1993_;
v_isShared_2006_ = v_isSharedCheck_2011_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_val_2003_);
lean_inc(v_key_2002_);
lean_dec(v_v_1993_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2011_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
lean_inc(v_f_1988_);
v___x_2007_ = lean_apply_1(v_f_1988_, v_val_2003_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___x_2007_);
v___x_2009_ = v___x_2005_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_key_2002_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
v___y_1997_ = v___x_2009_;
goto v___jp_1996_;
}
}
}
case 1:
{
lean_object* v_node_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
v_node_2012_ = lean_ctor_get(v_v_1993_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_v_1993_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2014_ = v_v_1993_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_node_2012_);
lean_dec(v_v_1993_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
lean_inc(v_f_1988_);
v___x_2016_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_1988_, v_node_2012_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
v___y_1997_ = v___x_2018_;
goto v___jp_1996_;
}
}
}
default: 
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_box(2);
v___y_1997_ = v___x_2021_;
goto v___jp_1996_;
}
}
v___jp_1996_:
{
size_t v___x_1998_; size_t v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = ((size_t)1ULL);
v___x_1999_ = lean_usize_add(v_i_1990_, v___x_1998_);
v___x_2000_ = lean_array_uset(v_bs_x27_1995_, v_i_1990_, v___y_1997_);
v_i_1990_ = v___x_1999_;
v_bs_1991_ = v___x_2000_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2022_, lean_object* v_n_2023_){
_start:
{
if (lean_obj_tag(v_n_2023_) == 0)
{
lean_object* v_es_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2034_; 
v_es_2024_ = lean_ctor_get(v_n_2023_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_n_2023_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2026_ = v_n_2023_;
v_isShared_2027_ = v_isSharedCheck_2034_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_es_2024_);
lean_dec(v_n_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2034_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
size_t v_sz_2028_; size_t v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v_sz_2028_ = lean_array_size(v_es_2024_);
v___x_2029_ = ((size_t)0ULL);
v___x_2030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(v_f_2022_, v_sz_2028_, v___x_2029_, v_es_2024_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2030_);
v___x_2032_ = v___x_2026_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
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
lean_object* v_ks_2035_; lean_object* v_vs_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2044_; 
v_ks_2035_ = lean_ctor_get(v_n_2023_, 0);
v_vs_2036_ = lean_ctor_get(v_n_2023_, 1);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_n_2023_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2038_ = v_n_2023_;
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_vs_2036_);
lean_inc(v_ks_2035_);
lean_dec(v_n_2023_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v_val_2040_; lean_object* v___x_2042_; 
v_val_2040_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(v_f_2022_, v_vs_2036_);
lean_dec_ref(v_vs_2036_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 1, v_val_2040_);
v___x_2042_ = v___x_2038_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_ks_2035_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_val_2040_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg___boxed(lean_object* v_f_2045_, lean_object* v_sz_2046_, lean_object* v_i_2047_, lean_object* v_bs_2048_){
_start:
{
size_t v_sz_boxed_2049_; size_t v_i_boxed_2050_; lean_object* v_res_2051_; 
v_sz_boxed_2049_ = lean_unbox_usize(v_sz_2046_);
lean_dec(v_sz_2046_);
v_i_boxed_2050_ = lean_unbox_usize(v_i_2047_);
lean_dec(v_i_2047_);
v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(v_f_2045_, v_sz_boxed_2049_, v_i_boxed_2050_, v_bs_2048_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(lean_object* v_pm_2052_, lean_object* v_f_2053_){
_start:
{
lean_object* v___f_2054_; lean_object* v___x_2055_; 
v___f_2054_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2054_, 0, v_f_2053_);
v___x_2055_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v___f_2054_, v_pm_2052_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(lean_object* v___x_2056_, size_t v_sz_2057_, size_t v_i_2058_, lean_object* v_bs_2059_){
_start:
{
uint8_t v___x_2060_; 
v___x_2060_ = lean_usize_dec_lt(v_i_2058_, v_sz_2057_);
if (v___x_2060_ == 0)
{
return v_bs_2059_;
}
else
{
lean_object* v_v_2061_; lean_object* v___x_2062_; lean_object* v_bs_x27_2063_; lean_object* v___y_2065_; 
v_v_2061_ = lean_array_uget(v_bs_2059_, v_i_2058_);
v___x_2062_ = lean_unsigned_to_nat(0u);
v_bs_x27_2063_ = lean_array_uset(v_bs_2059_, v_i_2058_, v___x_2062_);
if (lean_obj_tag(v_v_2061_) == 0)
{
v___y_2065_ = v_v_2061_;
goto v___jp_2064_;
}
else
{
lean_object* v_val_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2078_; 
v_val_2070_ = lean_ctor_get(v_v_2061_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_v_2061_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2072_ = v_v_2061_;
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_val_2070_);
lean_dec(v_v_2061_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2074_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_val_2070_, v___x_2056_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2074_);
v___x_2076_ = v___x_2072_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
v___y_2065_ = v___x_2076_;
goto v___jp_2064_;
}
}
}
v___jp_2064_:
{
size_t v___x_2066_; size_t v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = ((size_t)1ULL);
v___x_2067_ = lean_usize_add(v_i_2058_, v___x_2066_);
v___x_2068_ = lean_array_uset(v_bs_x27_2063_, v_i_2058_, v___y_2065_);
v_i_2058_ = v___x_2067_;
v_bs_2059_ = v___x_2068_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12___boxed(lean_object* v___x_2079_, lean_object* v_sz_2080_, lean_object* v_i_2081_, lean_object* v_bs_2082_){
_start:
{
size_t v_sz_boxed_2083_; size_t v_i_boxed_2084_; lean_object* v_res_2085_; 
v_sz_boxed_2083_ = lean_unbox_usize(v_sz_2080_);
lean_dec(v_sz_2080_);
v_i_boxed_2084_ = lean_unbox_usize(v_i_2081_);
lean_dec(v_i_2081_);
v_res_2085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_2079_, v_sz_boxed_2083_, v_i_boxed_2084_, v_bs_2082_);
lean_dec_ref(v___x_2079_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(lean_object* v___x_2086_, size_t v_sz_2087_, size_t v_i_2088_, lean_object* v_bs_2089_){
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
lean_object* v_v_2091_; lean_object* v___x_2092_; lean_object* v_bs_x27_2093_; lean_object* v___x_2094_; size_t v___x_2095_; size_t v___x_2096_; lean_object* v___x_2097_; 
v_v_2091_ = lean_array_uget(v_bs_2089_, v_i_2088_);
v___x_2092_ = lean_unsigned_to_nat(0u);
v_bs_x27_2093_ = lean_array_uset(v_bs_2089_, v_i_2088_, v___x_2092_);
v___x_2094_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_2086_, v_v_2091_);
v___x_2095_ = ((size_t)1ULL);
v___x_2096_ = lean_usize_add(v_i_2088_, v___x_2095_);
v___x_2097_ = lean_array_uset(v_bs_x27_2093_, v_i_2088_, v___x_2094_);
v_i_2088_ = v___x_2096_;
v_bs_2089_ = v___x_2097_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(lean_object* v___x_2099_, lean_object* v_x_2100_){
_start:
{
if (lean_obj_tag(v_x_2100_) == 0)
{
lean_object* v_cs_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2111_; 
v_cs_2101_ = lean_ctor_get(v_x_2100_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_x_2100_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2103_ = v_x_2100_;
v_isShared_2104_ = v_isSharedCheck_2111_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_cs_2101_);
lean_dec(v_x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2111_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
size_t v_sz_2105_; size_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2109_; 
v_sz_2105_ = lean_array_size(v_cs_2101_);
v___x_2106_ = ((size_t)0ULL);
v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(v___x_2099_, v_sz_2105_, v___x_2106_, v_cs_2101_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2107_);
v___x_2109_ = v___x_2103_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
else
{
lean_object* v_vs_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2122_; 
v_vs_2112_ = lean_ctor_get(v_x_2100_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_x_2100_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2114_ = v_x_2100_;
v_isShared_2115_ = v_isSharedCheck_2122_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_vs_2112_);
lean_dec(v_x_2100_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2122_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
size_t v_sz_2116_; size_t v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2120_; 
v_sz_2116_ = lean_array_size(v_vs_2112_);
v___x_2117_ = ((size_t)0ULL);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_2099_, v_sz_2116_, v___x_2117_, v_vs_2112_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v___x_2118_);
v___x_2120_ = v___x_2114_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11___boxed(lean_object* v___x_2123_, lean_object* v_x_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_2123_, v_x_2124_);
lean_dec_ref(v___x_2123_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16___boxed(lean_object* v___x_2126_, lean_object* v_sz_2127_, lean_object* v_i_2128_, lean_object* v_bs_2129_){
_start:
{
size_t v_sz_boxed_2130_; size_t v_i_boxed_2131_; lean_object* v_res_2132_; 
v_sz_boxed_2130_ = lean_unbox_usize(v_sz_2127_);
lean_dec(v_sz_2127_);
v_i_boxed_2131_ = lean_unbox_usize(v_i_2128_);
lean_dec(v_i_2128_);
v_res_2132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(v___x_2126_, v_sz_boxed_2130_, v_i_boxed_2131_, v_bs_2129_);
lean_dec_ref(v___x_2126_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(lean_object* v___x_2133_, lean_object* v_t_2134_){
_start:
{
lean_object* v_root_2135_; lean_object* v_tail_2136_; lean_object* v_size_2137_; size_t v_shift_2138_; lean_object* v_tailOff_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2150_; 
v_root_2135_ = lean_ctor_get(v_t_2134_, 0);
v_tail_2136_ = lean_ctor_get(v_t_2134_, 1);
v_size_2137_ = lean_ctor_get(v_t_2134_, 2);
v_shift_2138_ = lean_ctor_get_usize(v_t_2134_, 4);
v_tailOff_2139_ = lean_ctor_get(v_t_2134_, 3);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_t_2134_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2141_ = v_t_2134_;
v_isShared_2142_ = v_isSharedCheck_2150_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_tailOff_2139_);
lean_inc(v_size_2137_);
lean_inc(v_tail_2136_);
lean_inc(v_root_2135_);
lean_dec(v_t_2134_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2150_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; size_t v_sz_2144_; size_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2143_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_2133_, v_root_2135_);
v_sz_2144_ = lean_array_size(v_tail_2136_);
v___x_2145_ = ((size_t)0ULL);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_2133_, v_sz_2144_, v___x_2145_, v_tail_2136_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 1, v___x_2146_);
lean_ctor_set(v___x_2141_, 0, v___x_2143_);
v___x_2148_ = v___x_2141_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_size_2137_);
lean_ctor_set(v_reuseFailAlloc_2149_, 3, v_tailOff_2139_);
lean_ctor_set_usize(v_reuseFailAlloc_2149_, 4, v_shift_2138_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4___boxed(lean_object* v___x_2151_, lean_object* v_t_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v___x_2151_, v_t_2152_);
lean_dec_ref(v___x_2151_);
return v_res_2153_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = lean_unsigned_to_nat(32u);
v___x_2155_ = lean_mk_empty_array_with_capacity(v___x_2154_);
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
return v___x_2156_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1(void){
_start:
{
size_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2157_ = ((size_t)5ULL);
v___x_2158_ = lean_unsigned_to_nat(0u);
v___x_2159_ = lean_unsigned_to_nat(32u);
v___x_2160_ = lean_mk_empty_array_with_capacity(v___x_2159_);
v___x_2161_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0);
v___x_2162_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v___x_2160_);
lean_ctor_set(v___x_2162_, 2, v___x_2158_);
lean_ctor_set(v___x_2162_, 3, v___x_2158_);
lean_ctor_set_usize(v___x_2162_, 4, v___x_2157_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(size_t v_sz_2163_, size_t v_i_2164_, lean_object* v_bs_2165_){
_start:
{
uint8_t v___x_2166_; 
v___x_2166_ = lean_usize_dec_lt(v_i_2164_, v_sz_2163_);
if (v___x_2166_ == 0)
{
return v_bs_2165_;
}
else
{
lean_object* v___x_2167_; lean_object* v_bs_x27_2168_; lean_object* v___x_2169_; size_t v___x_2170_; size_t v___x_2171_; lean_object* v___x_2172_; 
v___x_2167_ = lean_unsigned_to_nat(0u);
v_bs_x27_2168_ = lean_array_uset(v_bs_2165_, v_i_2164_, v___x_2167_);
v___x_2169_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1);
v___x_2170_ = ((size_t)1ULL);
v___x_2171_ = lean_usize_add(v_i_2164_, v___x_2170_);
v___x_2172_ = lean_array_uset(v_bs_x27_2168_, v_i_2164_, v___x_2169_);
v_i_2164_ = v___x_2171_;
v_bs_2165_ = v___x_2172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___boxed(lean_object* v_sz_2174_, lean_object* v_i_2175_, lean_object* v_bs_2176_){
_start:
{
size_t v_sz_boxed_2177_; size_t v_i_boxed_2178_; lean_object* v_res_2179_; 
v_sz_boxed_2177_ = lean_unbox_usize(v_sz_2174_);
lean_dec(v_sz_2174_);
v_i_boxed_2178_ = lean_unbox_usize(v_i_2175_);
lean_dec(v_i_2175_);
v_res_2179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_boxed_2177_, v_i_boxed_2178_, v_bs_2176_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(size_t v_sz_2180_, size_t v_i_2181_, lean_object* v_bs_2182_){
_start:
{
uint8_t v___x_2183_; 
v___x_2183_ = lean_usize_dec_lt(v_i_2181_, v_sz_2180_);
if (v___x_2183_ == 0)
{
return v_bs_2182_;
}
else
{
lean_object* v_v_2184_; lean_object* v___x_2185_; lean_object* v_bs_x27_2186_; lean_object* v___x_2187_; size_t v___x_2188_; size_t v___x_2189_; lean_object* v___x_2190_; 
v_v_2184_ = lean_array_uget(v_bs_2182_, v_i_2181_);
v___x_2185_ = lean_unsigned_to_nat(0u);
v_bs_x27_2186_ = lean_array_uset(v_bs_2182_, v_i_2181_, v___x_2185_);
v___x_2187_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(v_v_2184_);
v___x_2188_ = ((size_t)1ULL);
v___x_2189_ = lean_usize_add(v_i_2181_, v___x_2188_);
v___x_2190_ = lean_array_uset(v_bs_x27_2186_, v_i_2181_, v___x_2187_);
v_i_2181_ = v___x_2189_;
v_bs_2182_ = v___x_2190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(lean_object* v_x_2192_){
_start:
{
if (lean_obj_tag(v_x_2192_) == 0)
{
lean_object* v_cs_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2203_; 
v_cs_2193_ = lean_ctor_get(v_x_2192_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_x_2192_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2195_ = v_x_2192_;
v_isShared_2196_ = v_isSharedCheck_2203_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_cs_2193_);
lean_dec(v_x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2203_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
size_t v_sz_2197_; size_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v_sz_2197_ = lean_array_size(v_cs_2193_);
v___x_2198_ = ((size_t)0ULL);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(v_sz_2197_, v___x_2198_, v_cs_2193_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2199_);
v___x_2201_ = v___x_2195_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_vs_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2214_; 
v_vs_2204_ = lean_ctor_get(v_x_2192_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_x_2192_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2206_ = v_x_2192_;
v_isShared_2207_ = v_isSharedCheck_2214_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_vs_2204_);
lean_dec(v_x_2192_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2214_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
size_t v_sz_2208_; size_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v_sz_2208_ = lean_array_size(v_vs_2204_);
v___x_2209_ = ((size_t)0ULL);
v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_2208_, v___x_2209_, v_vs_2204_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2210_);
v___x_2212_ = v___x_2206_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12___boxed(lean_object* v_sz_2215_, lean_object* v_i_2216_, lean_object* v_bs_2217_){
_start:
{
size_t v_sz_boxed_2218_; size_t v_i_boxed_2219_; lean_object* v_res_2220_; 
v_sz_boxed_2218_ = lean_unbox_usize(v_sz_2215_);
lean_dec(v_sz_2215_);
v_i_boxed_2219_ = lean_unbox_usize(v_i_2216_);
lean_dec(v_i_2216_);
v_res_2220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(v_sz_boxed_2218_, v_i_boxed_2219_, v_bs_2217_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(lean_object* v_t_2221_){
_start:
{
lean_object* v_root_2222_; lean_object* v_tail_2223_; lean_object* v_size_2224_; size_t v_shift_2225_; lean_object* v_tailOff_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2237_; 
v_root_2222_ = lean_ctor_get(v_t_2221_, 0);
v_tail_2223_ = lean_ctor_get(v_t_2221_, 1);
v_size_2224_ = lean_ctor_get(v_t_2221_, 2);
v_shift_2225_ = lean_ctor_get_usize(v_t_2221_, 4);
v_tailOff_2226_ = lean_ctor_get(v_t_2221_, 3);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_t_2221_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2228_ = v_t_2221_;
v_isShared_2229_ = v_isSharedCheck_2237_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_tailOff_2226_);
lean_inc(v_size_2224_);
lean_inc(v_tail_2223_);
lean_inc(v_root_2222_);
lean_dec(v_t_2221_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2237_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; size_t v_sz_2231_; size_t v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2230_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(v_root_2222_);
v_sz_2231_ = lean_array_size(v_tail_2223_);
v___x_2232_ = ((size_t)0ULL);
v___x_2233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_2231_, v___x_2232_, v_tail_2223_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 1, v___x_2233_);
lean_ctor_set(v___x_2228_, 0, v___x_2230_);
v___x_2235_ = v___x_2228_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_size_2224_);
lean_ctor_set(v_reuseFailAlloc_2236_, 3, v_tailOff_2226_);
lean_ctor_set_usize(v_reuseFailAlloc_2236_, 4, v_shift_2225_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = lean_unsigned_to_nat(32u);
v___x_2239_ = lean_mk_empty_array_with_capacity(v___x_2238_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1(void){
_start:
{
size_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2241_ = ((size_t)5ULL);
v___x_2242_ = lean_unsigned_to_nat(0u);
v___x_2243_ = lean_unsigned_to_nat(32u);
v___x_2244_ = lean_mk_empty_array_with_capacity(v___x_2243_);
v___x_2245_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0);
v___x_2246_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
lean_ctor_set(v___x_2246_, 1, v___x_2244_);
lean_ctor_set(v___x_2246_, 2, v___x_2242_);
lean_ctor_set(v___x_2246_, 3, v___x_2242_);
lean_ctor_set_usize(v___x_2246_, 4, v___x_2241_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(size_t v_sz_2247_, size_t v_i_2248_, lean_object* v_bs_2249_){
_start:
{
uint8_t v___x_2250_; 
v___x_2250_ = lean_usize_dec_lt(v_i_2248_, v_sz_2247_);
if (v___x_2250_ == 0)
{
return v_bs_2249_;
}
else
{
lean_object* v___x_2251_; lean_object* v_bs_x27_2252_; lean_object* v___x_2253_; size_t v___x_2254_; size_t v___x_2255_; lean_object* v___x_2256_; 
v___x_2251_ = lean_unsigned_to_nat(0u);
v_bs_x27_2252_ = lean_array_uset(v_bs_2249_, v_i_2248_, v___x_2251_);
v___x_2253_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1);
v___x_2254_ = ((size_t)1ULL);
v___x_2255_ = lean_usize_add(v_i_2248_, v___x_2254_);
v___x_2256_ = lean_array_uset(v_bs_x27_2252_, v_i_2248_, v___x_2253_);
v_i_2248_ = v___x_2255_;
v_bs_2249_ = v___x_2256_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___boxed(lean_object* v_sz_2258_, lean_object* v_i_2259_, lean_object* v_bs_2260_){
_start:
{
size_t v_sz_boxed_2261_; size_t v_i_boxed_2262_; lean_object* v_res_2263_; 
v_sz_boxed_2261_ = lean_unbox_usize(v_sz_2258_);
lean_dec(v_sz_2258_);
v_i_boxed_2262_ = lean_unbox_usize(v_i_2259_);
lean_dec(v_i_2259_);
v_res_2263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_boxed_2261_, v_i_boxed_2262_, v_bs_2260_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(size_t v_sz_2264_, size_t v_i_2265_, lean_object* v_bs_2266_){
_start:
{
uint8_t v___x_2267_; 
v___x_2267_ = lean_usize_dec_lt(v_i_2265_, v_sz_2264_);
if (v___x_2267_ == 0)
{
return v_bs_2266_;
}
else
{
lean_object* v_v_2268_; lean_object* v___x_2269_; lean_object* v_bs_x27_2270_; lean_object* v___x_2271_; size_t v___x_2272_; size_t v___x_2273_; lean_object* v___x_2274_; 
v_v_2268_ = lean_array_uget(v_bs_2266_, v_i_2265_);
v___x_2269_ = lean_unsigned_to_nat(0u);
v_bs_x27_2270_ = lean_array_uset(v_bs_2266_, v_i_2265_, v___x_2269_);
v___x_2271_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(v_v_2268_);
v___x_2272_ = ((size_t)1ULL);
v___x_2273_ = lean_usize_add(v_i_2265_, v___x_2272_);
v___x_2274_ = lean_array_uset(v_bs_x27_2270_, v_i_2265_, v___x_2271_);
v_i_2265_ = v___x_2273_;
v_bs_2266_ = v___x_2274_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(lean_object* v_x_2276_){
_start:
{
if (lean_obj_tag(v_x_2276_) == 0)
{
lean_object* v_cs_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2287_; 
v_cs_2277_ = lean_ctor_get(v_x_2276_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_x_2276_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2279_ = v_x_2276_;
v_isShared_2280_ = v_isSharedCheck_2287_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_cs_2277_);
lean_dec(v_x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2287_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
size_t v_sz_2281_; size_t v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
v_sz_2281_ = lean_array_size(v_cs_2277_);
v___x_2282_ = ((size_t)0ULL);
v___x_2283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(v_sz_2281_, v___x_2282_, v_cs_2277_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2283_);
v___x_2285_ = v___x_2279_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_vs_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2298_; 
v_vs_2288_ = lean_ctor_get(v_x_2276_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_x_2276_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2290_ = v_x_2276_;
v_isShared_2291_ = v_isSharedCheck_2298_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_vs_2288_);
lean_dec(v_x_2276_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2298_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
size_t v_sz_2292_; size_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
v_sz_2292_ = lean_array_size(v_vs_2288_);
v___x_2293_ = ((size_t)0ULL);
v___x_2294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_2292_, v___x_2293_, v_vs_2288_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2294_);
v___x_2296_ = v___x_2290_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8___boxed(lean_object* v_sz_2299_, lean_object* v_i_2300_, lean_object* v_bs_2301_){
_start:
{
size_t v_sz_boxed_2302_; size_t v_i_boxed_2303_; lean_object* v_res_2304_; 
v_sz_boxed_2302_ = lean_unbox_usize(v_sz_2299_);
lean_dec(v_sz_2299_);
v_i_boxed_2303_ = lean_unbox_usize(v_i_2300_);
lean_dec(v_i_2300_);
v_res_2304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(v_sz_boxed_2302_, v_i_boxed_2303_, v_bs_2301_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(lean_object* v_t_2305_){
_start:
{
lean_object* v_root_2306_; lean_object* v_tail_2307_; lean_object* v_size_2308_; size_t v_shift_2309_; lean_object* v_tailOff_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2321_; 
v_root_2306_ = lean_ctor_get(v_t_2305_, 0);
v_tail_2307_ = lean_ctor_get(v_t_2305_, 1);
v_size_2308_ = lean_ctor_get(v_t_2305_, 2);
v_shift_2309_ = lean_ctor_get_usize(v_t_2305_, 4);
v_tailOff_2310_ = lean_ctor_get(v_t_2305_, 3);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_t_2305_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2312_ = v_t_2305_;
v_isShared_2313_ = v_isSharedCheck_2321_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_tailOff_2310_);
lean_inc(v_size_2308_);
lean_inc(v_tail_2307_);
lean_inc(v_root_2306_);
lean_dec(v_t_2305_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2321_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; size_t v_sz_2315_; size_t v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2314_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(v_root_2306_);
v_sz_2315_ = lean_array_size(v_tail_2307_);
v___x_2316_ = ((size_t)0ULL);
v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_2315_, v___x_2316_, v_tail_2307_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 1, v___x_2317_);
lean_ctor_set(v___x_2312_, 0, v___x_2314_);
v___x_2319_ = v___x_2312_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2314_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_size_2308_);
lean_ctor_set(v_reuseFailAlloc_2320_, 3, v_tailOff_2310_);
lean_ctor_set_usize(v_reuseFailAlloc_2320_, 4, v_shift_2309_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(size_t v_sz_2322_, size_t v_i_2323_, lean_object* v_bs_2324_){
_start:
{
uint8_t v___x_2325_; 
v___x_2325_ = lean_usize_dec_lt(v_i_2323_, v_sz_2322_);
if (v___x_2325_ == 0)
{
return v_bs_2324_;
}
else
{
lean_object* v___x_2326_; lean_object* v_bs_x27_2327_; lean_object* v___x_2328_; size_t v___x_2329_; size_t v___x_2330_; lean_object* v___x_2331_; 
v___x_2326_ = lean_unsigned_to_nat(0u);
v_bs_x27_2327_ = lean_array_uset(v_bs_2324_, v_i_2323_, v___x_2326_);
v___x_2328_ = lean_box(1);
v___x_2329_ = ((size_t)1ULL);
v___x_2330_ = lean_usize_add(v_i_2323_, v___x_2329_);
v___x_2331_ = lean_array_uset(v_bs_x27_2327_, v_i_2323_, v___x_2328_);
v_i_2323_ = v___x_2330_;
v_bs_2324_ = v___x_2331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16___boxed(lean_object* v_sz_2333_, lean_object* v_i_2334_, lean_object* v_bs_2335_){
_start:
{
size_t v_sz_boxed_2336_; size_t v_i_boxed_2337_; lean_object* v_res_2338_; 
v_sz_boxed_2336_ = lean_unbox_usize(v_sz_2333_);
lean_dec(v_sz_2333_);
v_i_boxed_2337_ = lean_unbox_usize(v_i_2334_);
lean_dec(v_i_2334_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_boxed_2336_, v_i_boxed_2337_, v_bs_2335_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(size_t v_sz_2339_, size_t v_i_2340_, lean_object* v_bs_2341_){
_start:
{
uint8_t v___x_2342_; 
v___x_2342_ = lean_usize_dec_lt(v_i_2340_, v_sz_2339_);
if (v___x_2342_ == 0)
{
return v_bs_2341_;
}
else
{
lean_object* v_v_2343_; lean_object* v___x_2344_; lean_object* v_bs_x27_2345_; lean_object* v___x_2346_; size_t v___x_2347_; size_t v___x_2348_; lean_object* v___x_2349_; 
v_v_2343_ = lean_array_uget(v_bs_2341_, v_i_2340_);
v___x_2344_ = lean_unsigned_to_nat(0u);
v_bs_x27_2345_ = lean_array_uset(v_bs_2341_, v_i_2340_, v___x_2344_);
v___x_2346_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(v_v_2343_);
v___x_2347_ = ((size_t)1ULL);
v___x_2348_ = lean_usize_add(v_i_2340_, v___x_2347_);
v___x_2349_ = lean_array_uset(v_bs_x27_2345_, v_i_2340_, v___x_2346_);
v_i_2340_ = v___x_2348_;
v_bs_2341_ = v___x_2349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(lean_object* v_x_2351_){
_start:
{
if (lean_obj_tag(v_x_2351_) == 0)
{
lean_object* v_cs_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2362_; 
v_cs_2352_ = lean_ctor_get(v_x_2351_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_x_2351_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2354_ = v_x_2351_;
v_isShared_2355_ = v_isSharedCheck_2362_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_cs_2352_);
lean_dec(v_x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2362_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
size_t v_sz_2356_; size_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2360_; 
v_sz_2356_ = lean_array_size(v_cs_2352_);
v___x_2357_ = ((size_t)0ULL);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(v_sz_2356_, v___x_2357_, v_cs_2352_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2358_);
v___x_2360_ = v___x_2354_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_vs_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2373_; 
v_vs_2363_ = lean_ctor_get(v_x_2351_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_x_2351_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2365_ = v_x_2351_;
v_isShared_2366_ = v_isSharedCheck_2373_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_vs_2363_);
lean_dec(v_x_2351_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2373_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
size_t v_sz_2367_; size_t v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
v_sz_2367_ = lean_array_size(v_vs_2363_);
v___x_2368_ = ((size_t)0ULL);
v___x_2369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_2367_, v___x_2368_, v_vs_2363_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2369_);
v___x_2371_ = v___x_2365_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21___boxed(lean_object* v_sz_2374_, lean_object* v_i_2375_, lean_object* v_bs_2376_){
_start:
{
size_t v_sz_boxed_2377_; size_t v_i_boxed_2378_; lean_object* v_res_2379_; 
v_sz_boxed_2377_ = lean_unbox_usize(v_sz_2374_);
lean_dec(v_sz_2374_);
v_i_boxed_2378_ = lean_unbox_usize(v_i_2375_);
lean_dec(v_i_2375_);
v_res_2379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(v_sz_boxed_2377_, v_i_boxed_2378_, v_bs_2376_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(lean_object* v_t_2380_){
_start:
{
lean_object* v_root_2381_; lean_object* v_tail_2382_; lean_object* v_size_2383_; size_t v_shift_2384_; lean_object* v_tailOff_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2396_; 
v_root_2381_ = lean_ctor_get(v_t_2380_, 0);
v_tail_2382_ = lean_ctor_get(v_t_2380_, 1);
v_size_2383_ = lean_ctor_get(v_t_2380_, 2);
v_shift_2384_ = lean_ctor_get_usize(v_t_2380_, 4);
v_tailOff_2385_ = lean_ctor_get(v_t_2380_, 3);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_t_2380_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2387_ = v_t_2380_;
v_isShared_2388_ = v_isSharedCheck_2396_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_tailOff_2385_);
lean_inc(v_size_2383_);
lean_inc(v_tail_2382_);
lean_inc(v_root_2381_);
lean_dec(v_t_2380_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2396_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2389_; size_t v_sz_2390_; size_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2389_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(v_root_2381_);
v_sz_2390_ = lean_array_size(v_tail_2382_);
v___x_2391_ = ((size_t)0ULL);
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_2390_, v___x_2391_, v_tail_2382_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 1, v___x_2392_);
lean_ctor_set(v___x_2387_, 0, v___x_2389_);
v___x_2394_ = v___x_2387_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2389_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_size_2383_);
lean_ctor_set(v_reuseFailAlloc_2395_, 3, v_tailOff_2385_);
lean_ctor_set_usize(v_reuseFailAlloc_2395_, 4, v_shift_2384_);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(lean_object* v___x_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
if (lean_obj_tag(v_a_2398_) == 0)
{
lean_object* v___x_2400_; 
v___x_2400_ = l_List_reverse___redArg(v_a_2399_);
return v___x_2400_;
}
else
{
lean_object* v_head_2401_; lean_object* v_tail_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2412_; 
v_head_2401_ = lean_ctor_get(v_a_2398_, 0);
v_tail_2402_ = lean_ctor_get(v_a_2398_, 1);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_a_2398_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2404_ = v_a_2398_;
v_isShared_2405_ = v_isSharedCheck_2412_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_tail_2402_);
lean_inc(v_head_2401_);
lean_dec(v_a_2398_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2412_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2406_ = lean_unsigned_to_nat(0u);
v___x_2407_ = lean_array_get_borrowed(v___x_2406_, v___x_2397_, v_head_2401_);
lean_dec(v_head_2401_);
lean_inc(v___x_2407_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 1, v_a_2399_);
lean_ctor_set(v___x_2404_, 0, v___x_2407_);
v___x_2409_ = v___x_2404_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_a_2399_);
v___x_2409_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
v_a_2398_ = v_tail_2402_;
v_a_2399_ = v___x_2409_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(lean_object* v___x_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2413_, v_a_2414_, v_a_2415_);
lean_dec_ref(v___x_2413_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(size_t v_sz_2417_, size_t v_i_2418_, lean_object* v_bs_2419_){
_start:
{
uint8_t v___x_2420_; 
v___x_2420_ = lean_usize_dec_lt(v_i_2418_, v_sz_2417_);
if (v___x_2420_ == 0)
{
return v_bs_2419_;
}
else
{
lean_object* v___x_2421_; lean_object* v_bs_x27_2422_; lean_object* v___x_2423_; size_t v___x_2424_; size_t v___x_2425_; lean_object* v___x_2426_; 
v___x_2421_ = lean_unsigned_to_nat(0u);
v_bs_x27_2422_ = lean_array_uset(v_bs_2419_, v_i_2418_, v___x_2421_);
v___x_2423_ = lean_box(0);
v___x_2424_ = ((size_t)1ULL);
v___x_2425_ = lean_usize_add(v_i_2418_, v___x_2424_);
v___x_2426_ = lean_array_uset(v_bs_x27_2422_, v_i_2418_, v___x_2423_);
v_i_2418_ = v___x_2425_;
v_bs_2419_ = v___x_2426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3___boxed(lean_object* v_sz_2428_, lean_object* v_i_2429_, lean_object* v_bs_2430_){
_start:
{
size_t v_sz_boxed_2431_; size_t v_i_boxed_2432_; lean_object* v_res_2433_; 
v_sz_boxed_2431_ = lean_unbox_usize(v_sz_2428_);
lean_dec(v_sz_2428_);
v_i_boxed_2432_ = lean_unbox_usize(v_i_2429_);
lean_dec(v_i_2429_);
v_res_2433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_boxed_2431_, v_i_boxed_2432_, v_bs_2430_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(size_t v_sz_2434_, size_t v_i_2435_, lean_object* v_bs_2436_){
_start:
{
uint8_t v___x_2437_; 
v___x_2437_ = lean_usize_dec_lt(v_i_2435_, v_sz_2434_);
if (v___x_2437_ == 0)
{
return v_bs_2436_;
}
else
{
lean_object* v_v_2438_; lean_object* v___x_2439_; lean_object* v_bs_x27_2440_; lean_object* v___x_2441_; size_t v___x_2442_; size_t v___x_2443_; lean_object* v___x_2444_; 
v_v_2438_ = lean_array_uget(v_bs_2436_, v_i_2435_);
v___x_2439_ = lean_unsigned_to_nat(0u);
v_bs_x27_2440_ = lean_array_uset(v_bs_2436_, v_i_2435_, v___x_2439_);
v___x_2441_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_v_2438_);
v___x_2442_ = ((size_t)1ULL);
v___x_2443_ = lean_usize_add(v_i_2435_, v___x_2442_);
v___x_2444_ = lean_array_uset(v_bs_x27_2440_, v_i_2435_, v___x_2441_);
v_i_2435_ = v___x_2443_;
v_bs_2436_ = v___x_2444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(lean_object* v_x_2446_){
_start:
{
if (lean_obj_tag(v_x_2446_) == 0)
{
lean_object* v_cs_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2457_; 
v_cs_2447_ = lean_ctor_get(v_x_2446_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_x_2446_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2449_ = v_x_2446_;
v_isShared_2450_ = v_isSharedCheck_2457_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_cs_2447_);
lean_dec(v_x_2446_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2457_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
size_t v_sz_2451_; size_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
v_sz_2451_ = lean_array_size(v_cs_2447_);
v___x_2452_ = ((size_t)0ULL);
v___x_2453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(v_sz_2451_, v___x_2452_, v_cs_2447_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2453_);
v___x_2455_ = v___x_2449_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
else
{
lean_object* v_vs_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2468_; 
v_vs_2458_ = lean_ctor_get(v_x_2446_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_x_2446_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2460_ = v_x_2446_;
v_isShared_2461_ = v_isSharedCheck_2468_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_vs_2458_);
lean_dec(v_x_2446_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2468_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
size_t v_sz_2462_; size_t v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v_sz_2462_ = lean_array_size(v_vs_2458_);
v___x_2463_ = ((size_t)0ULL);
v___x_2464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_2462_, v___x_2463_, v_vs_2458_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2464_);
v___x_2466_ = v___x_2460_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_2469_, lean_object* v_i_2470_, lean_object* v_bs_2471_){
_start:
{
size_t v_sz_boxed_2472_; size_t v_i_boxed_2473_; lean_object* v_res_2474_; 
v_sz_boxed_2472_ = lean_unbox_usize(v_sz_2469_);
lean_dec(v_sz_2469_);
v_i_boxed_2473_ = lean_unbox_usize(v_i_2470_);
lean_dec(v_i_2470_);
v_res_2474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(v_sz_boxed_2472_, v_i_boxed_2473_, v_bs_2471_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(lean_object* v_t_2475_){
_start:
{
lean_object* v_root_2476_; lean_object* v_tail_2477_; lean_object* v_size_2478_; size_t v_shift_2479_; lean_object* v_tailOff_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2491_; 
v_root_2476_ = lean_ctor_get(v_t_2475_, 0);
v_tail_2477_ = lean_ctor_get(v_t_2475_, 1);
v_size_2478_ = lean_ctor_get(v_t_2475_, 2);
v_shift_2479_ = lean_ctor_get_usize(v_t_2475_, 4);
v_tailOff_2480_ = lean_ctor_get(v_t_2475_, 3);
v_isSharedCheck_2491_ = !lean_is_exclusive(v_t_2475_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2482_ = v_t_2475_;
v_isShared_2483_ = v_isSharedCheck_2491_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_tailOff_2480_);
lean_inc(v_size_2478_);
lean_inc(v_tail_2477_);
lean_inc(v_root_2476_);
lean_dec(v_t_2475_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2491_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; size_t v_sz_2485_; size_t v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2484_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_root_2476_);
v_sz_2485_ = lean_array_size(v_tail_2477_);
v___x_2486_ = ((size_t)0ULL);
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_2485_, v___x_2486_, v_tail_2477_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v___x_2487_);
lean_ctor_set(v___x_2482_, 0, v___x_2484_);
v___x_2489_ = v___x_2482_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v_size_2478_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v_tailOff_2480_);
lean_ctor_set_usize(v_reuseFailAlloc_2490_, 4, v_shift_2479_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(lean_object* v_a_2492_, lean_object* v___f_2493_, lean_object* v___x_2494_, lean_object* v_s_2495_){
_start:
{
lean_object* v_vars_2496_; lean_object* v_varMap_2497_; lean_object* v_natToIntMap_2498_; lean_object* v_natDef_2499_; lean_object* v_dvds_2500_; lean_object* v_lowers_2501_; lean_object* v_uppers_2502_; lean_object* v_diseqs_2503_; lean_object* v_elimEqs_2504_; lean_object* v_elimStack_2505_; lean_object* v_occurs_2506_; lean_object* v_assignment_2507_; lean_object* v_nextCnstrId_2508_; uint8_t v_caseSplits_2509_; lean_object* v_conflict_x3f_2510_; lean_object* v_divMod_2511_; lean_object* v_toIntIds_2512_; lean_object* v_toIntInfos_2513_; lean_object* v_toIntTermMap_2514_; lean_object* v_toIntVarMap_2515_; uint8_t v_usedCommRing_2516_; lean_object* v_nonlinearOccs_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2539_; 
v_vars_2496_ = lean_ctor_get(v_s_2495_, 0);
v_varMap_2497_ = lean_ctor_get(v_s_2495_, 1);
v_natToIntMap_2498_ = lean_ctor_get(v_s_2495_, 4);
v_natDef_2499_ = lean_ctor_get(v_s_2495_, 5);
v_dvds_2500_ = lean_ctor_get(v_s_2495_, 6);
v_lowers_2501_ = lean_ctor_get(v_s_2495_, 7);
v_uppers_2502_ = lean_ctor_get(v_s_2495_, 8);
v_diseqs_2503_ = lean_ctor_get(v_s_2495_, 9);
v_elimEqs_2504_ = lean_ctor_get(v_s_2495_, 10);
v_elimStack_2505_ = lean_ctor_get(v_s_2495_, 11);
v_occurs_2506_ = lean_ctor_get(v_s_2495_, 12);
v_assignment_2507_ = lean_ctor_get(v_s_2495_, 13);
v_nextCnstrId_2508_ = lean_ctor_get(v_s_2495_, 14);
v_caseSplits_2509_ = lean_ctor_get_uint8(v_s_2495_, sizeof(void*)*23);
v_conflict_x3f_2510_ = lean_ctor_get(v_s_2495_, 15);
v_divMod_2511_ = lean_ctor_get(v_s_2495_, 17);
v_toIntIds_2512_ = lean_ctor_get(v_s_2495_, 18);
v_toIntInfos_2513_ = lean_ctor_get(v_s_2495_, 19);
v_toIntTermMap_2514_ = lean_ctor_get(v_s_2495_, 20);
v_toIntVarMap_2515_ = lean_ctor_get(v_s_2495_, 21);
v_usedCommRing_2516_ = lean_ctor_get_uint8(v_s_2495_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2517_ = lean_ctor_get(v_s_2495_, 22);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_s_2495_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; lean_object* v_unused_2541_; lean_object* v_unused_2542_; 
v_unused_2540_ = lean_ctor_get(v_s_2495_, 16);
lean_dec(v_unused_2540_);
v_unused_2541_ = lean_ctor_get(v_s_2495_, 3);
lean_dec(v_unused_2541_);
v_unused_2542_ = lean_ctor_get(v_s_2495_, 2);
lean_dec(v_unused_2542_);
v___x_2519_ = v_s_2495_;
v_isShared_2520_ = v_isSharedCheck_2539_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_nonlinearOccs_2517_);
lean_inc(v_toIntVarMap_2515_);
lean_inc(v_toIntTermMap_2514_);
lean_inc(v_toIntInfos_2513_);
lean_inc(v_toIntIds_2512_);
lean_inc(v_divMod_2511_);
lean_inc(v_conflict_x3f_2510_);
lean_inc(v_nextCnstrId_2508_);
lean_inc(v_assignment_2507_);
lean_inc(v_occurs_2506_);
lean_inc(v_elimStack_2505_);
lean_inc(v_elimEqs_2504_);
lean_inc(v_diseqs_2503_);
lean_inc(v_uppers_2502_);
lean_inc(v_lowers_2501_);
lean_inc(v_dvds_2500_);
lean_inc(v_natDef_2499_);
lean_inc(v_natToIntMap_2498_);
lean_inc(v_varMap_2497_);
lean_inc(v_vars_2496_);
lean_dec(v_s_2495_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2539_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2521_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_a_2492_);
lean_inc_ref(v_vars_2496_);
v___x_2522_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2521_, v_vars_2496_, v_a_2492_);
lean_inc_ref(v___f_2493_);
lean_inc_ref(v_varMap_2497_);
v___x_2523_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_varMap_2497_, v___f_2493_);
v___x_2524_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_natDef_2499_, v___f_2493_);
v___x_2525_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(v_dvds_2500_);
v___x_2526_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v_lowers_2501_);
v___x_2527_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v_uppers_2502_);
v___x_2528_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_diseqs_2503_);
v___x_2529_ = lean_box(0);
v___x_2530_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(v___x_2529_, v_elimEqs_2504_, v_a_2492_);
v___x_2531_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v___x_2494_, v___x_2530_);
v___x_2532_ = lean_box(0);
v___x_2533_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(v___x_2494_, v_elimStack_2505_, v___x_2532_);
v___x_2534_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(v_occurs_2506_);
v___x_2535_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 16, v___x_2535_);
lean_ctor_set(v___x_2519_, 12, v___x_2534_);
lean_ctor_set(v___x_2519_, 11, v___x_2533_);
lean_ctor_set(v___x_2519_, 10, v___x_2531_);
lean_ctor_set(v___x_2519_, 9, v___x_2528_);
lean_ctor_set(v___x_2519_, 8, v___x_2527_);
lean_ctor_set(v___x_2519_, 7, v___x_2526_);
lean_ctor_set(v___x_2519_, 6, v___x_2525_);
lean_ctor_set(v___x_2519_, 5, v___x_2524_);
lean_ctor_set(v___x_2519_, 3, v_varMap_2497_);
lean_ctor_set(v___x_2519_, 2, v_vars_2496_);
lean_ctor_set(v___x_2519_, 1, v___x_2523_);
lean_ctor_set(v___x_2519_, 0, v___x_2522_);
v___x_2537_ = v___x_2519_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v___x_2523_);
lean_ctor_set(v_reuseFailAlloc_2538_, 2, v_vars_2496_);
lean_ctor_set(v_reuseFailAlloc_2538_, 3, v_varMap_2497_);
lean_ctor_set(v_reuseFailAlloc_2538_, 4, v_natToIntMap_2498_);
lean_ctor_set(v_reuseFailAlloc_2538_, 5, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2538_, 6, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2538_, 7, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2538_, 8, v___x_2527_);
lean_ctor_set(v_reuseFailAlloc_2538_, 9, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2538_, 10, v___x_2531_);
lean_ctor_set(v_reuseFailAlloc_2538_, 11, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2538_, 12, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2538_, 13, v_assignment_2507_);
lean_ctor_set(v_reuseFailAlloc_2538_, 14, v_nextCnstrId_2508_);
lean_ctor_set(v_reuseFailAlloc_2538_, 15, v_conflict_x3f_2510_);
lean_ctor_set(v_reuseFailAlloc_2538_, 16, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2538_, 17, v_divMod_2511_);
lean_ctor_set(v_reuseFailAlloc_2538_, 18, v_toIntIds_2512_);
lean_ctor_set(v_reuseFailAlloc_2538_, 19, v_toIntInfos_2513_);
lean_ctor_set(v_reuseFailAlloc_2538_, 20, v_toIntTermMap_2514_);
lean_ctor_set(v_reuseFailAlloc_2538_, 21, v_toIntVarMap_2515_);
lean_ctor_set(v_reuseFailAlloc_2538_, 22, v_nonlinearOccs_2517_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, sizeof(void*)*23, v_caseSplits_2509_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, sizeof(void*)*23 + 1, v_usedCommRing_2516_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(lean_object* v_a_2543_, lean_object* v___f_2544_, lean_object* v___x_2545_, lean_object* v_s_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(v_a_2543_, v___f_2544_, v___x_2545_, v_s_2546_);
lean_dec_ref(v___x_2545_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(lean_object* v_as_2548_, size_t v_i_2549_, size_t v_stop_2550_, lean_object* v_b_2551_){
_start:
{
lean_object* v___y_2553_; uint8_t v___x_2557_; 
v___x_2557_ = lean_usize_dec_eq(v_i_2549_, v_stop_2550_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_array_uget_borrowed(v_as_2548_, v_i_2549_);
if (lean_obj_tag(v___x_2558_) == 0)
{
v___y_2553_ = v_b_2551_;
goto v___jp_2552_;
}
else
{
lean_object* v_val_2559_; lean_object* v___x_2560_; 
v_val_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_val_2559_);
v___x_2560_ = lean_array_push(v_b_2551_, v_val_2559_);
v___y_2553_ = v___x_2560_;
goto v___jp_2552_;
}
}
else
{
return v_b_2551_;
}
v___jp_2552_:
{
size_t v___x_2554_; size_t v___x_2555_; 
v___x_2554_ = ((size_t)1ULL);
v___x_2555_ = lean_usize_add(v_i_2549_, v___x_2554_);
v_i_2549_ = v___x_2555_;
v_b_2551_ = v___y_2553_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19___boxed(lean_object* v_as_2561_, lean_object* v_i_2562_, lean_object* v_stop_2563_, lean_object* v_b_2564_){
_start:
{
size_t v_i_boxed_2565_; size_t v_stop_boxed_2566_; lean_object* v_res_2567_; 
v_i_boxed_2565_ = lean_unbox_usize(v_i_2562_);
lean_dec(v_i_2562_);
v_stop_boxed_2566_ = lean_unbox_usize(v_stop_2563_);
lean_dec(v_stop_2563_);
v_res_2567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_as_2561_, v_i_boxed_2565_, v_stop_boxed_2566_, v_b_2564_);
lean_dec_ref(v_as_2561_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(lean_object* v_x_2568_, lean_object* v_x_2569_){
_start:
{
if (lean_obj_tag(v_x_2568_) == 0)
{
lean_object* v_cs_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v_cs_2570_ = lean_ctor_get(v_x_2568_, 0);
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = lean_array_get_size(v_cs_2570_);
v___x_2573_ = lean_nat_dec_lt(v___x_2571_, v___x_2572_);
if (v___x_2573_ == 0)
{
return v_x_2569_;
}
else
{
uint8_t v___x_2574_; 
v___x_2574_ = lean_nat_dec_le(v___x_2572_, v___x_2572_);
if (v___x_2574_ == 0)
{
if (v___x_2573_ == 0)
{
return v_x_2569_;
}
else
{
size_t v___x_2575_; size_t v___x_2576_; lean_object* v___x_2577_; 
v___x_2575_ = ((size_t)0ULL);
v___x_2576_ = lean_usize_of_nat(v___x_2572_);
v___x_2577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_2570_, v___x_2575_, v___x_2576_, v_x_2569_);
return v___x_2577_;
}
}
else
{
size_t v___x_2578_; size_t v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = ((size_t)0ULL);
v___x_2579_ = lean_usize_of_nat(v___x_2572_);
v___x_2580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_2570_, v___x_2578_, v___x_2579_, v_x_2569_);
return v___x_2580_;
}
}
}
else
{
lean_object* v_vs_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v_vs_2581_ = lean_ctor_get(v_x_2568_, 0);
v___x_2582_ = lean_unsigned_to_nat(0u);
v___x_2583_ = lean_array_get_size(v_vs_2581_);
v___x_2584_ = lean_nat_dec_lt(v___x_2582_, v___x_2583_);
if (v___x_2584_ == 0)
{
return v_x_2569_;
}
else
{
uint8_t v___x_2585_; 
v___x_2585_ = lean_nat_dec_le(v___x_2583_, v___x_2583_);
if (v___x_2585_ == 0)
{
if (v___x_2584_ == 0)
{
return v_x_2569_;
}
else
{
size_t v___x_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = ((size_t)0ULL);
v___x_2587_ = lean_usize_of_nat(v___x_2583_);
v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2581_, v___x_2586_, v___x_2587_, v_x_2569_);
return v___x_2588_;
}
}
else
{
size_t v___x_2589_; size_t v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = ((size_t)0ULL);
v___x_2590_ = lean_usize_of_nat(v___x_2583_);
v___x_2591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2581_, v___x_2589_, v___x_2590_, v_x_2569_);
return v___x_2591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(lean_object* v_as_2592_, size_t v_i_2593_, size_t v_stop_2594_, lean_object* v_b_2595_){
_start:
{
uint8_t v___x_2596_; 
v___x_2596_ = lean_usize_dec_eq(v_i_2593_, v_stop_2594_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; size_t v___x_2599_; size_t v___x_2600_; 
v___x_2597_ = lean_array_uget_borrowed(v_as_2592_, v_i_2593_);
v___x_2598_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v___x_2597_, v_b_2595_);
v___x_2599_ = ((size_t)1ULL);
v___x_2600_ = lean_usize_add(v_i_2593_, v___x_2599_);
v_i_2593_ = v___x_2600_;
v_b_2595_ = v___x_2598_;
goto _start;
}
else
{
return v_b_2595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25___boxed(lean_object* v_as_2602_, lean_object* v_i_2603_, lean_object* v_stop_2604_, lean_object* v_b_2605_){
_start:
{
size_t v_i_boxed_2606_; size_t v_stop_boxed_2607_; lean_object* v_res_2608_; 
v_i_boxed_2606_ = lean_unbox_usize(v_i_2603_);
lean_dec(v_i_2603_);
v_stop_boxed_2607_ = lean_unbox_usize(v_stop_2604_);
lean_dec(v_stop_2604_);
v_res_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_as_2602_, v_i_boxed_2606_, v_stop_boxed_2607_, v_b_2605_);
lean_dec_ref(v_as_2602_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20___boxed(lean_object* v_x_2609_, lean_object* v_x_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v_x_2609_, v_x_2610_);
lean_dec_ref(v_x_2609_);
return v_res_2611_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0(void){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(lean_object* v_x_2613_, size_t v_x_2614_, size_t v_x_2615_, lean_object* v_x_2616_){
_start:
{
if (lean_obj_tag(v_x_2613_) == 0)
{
lean_object* v_cs_2617_; lean_object* v___x_2618_; size_t v___x_2619_; lean_object* v_j_2620_; lean_object* v___x_2621_; size_t v___x_2622_; size_t v___x_2623_; size_t v___x_2624_; size_t v___x_2625_; size_t v___x_2626_; size_t v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v_cs_2617_ = lean_ctor_get(v_x_2613_, 0);
v___x_2618_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
v___x_2619_ = lean_usize_shift_right(v_x_2614_, v_x_2615_);
v_j_2620_ = lean_usize_to_nat(v___x_2619_);
v___x_2621_ = lean_array_get_borrowed(v___x_2618_, v_cs_2617_, v_j_2620_);
v___x_2622_ = ((size_t)1ULL);
v___x_2623_ = lean_usize_shift_left(v___x_2622_, v_x_2615_);
v___x_2624_ = lean_usize_sub(v___x_2623_, v___x_2622_);
v___x_2625_ = lean_usize_land(v_x_2614_, v___x_2624_);
v___x_2626_ = ((size_t)5ULL);
v___x_2627_ = lean_usize_sub(v_x_2615_, v___x_2626_);
v___x_2628_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v___x_2621_, v___x_2625_, v___x_2627_, v_x_2616_);
v___x_2629_ = lean_unsigned_to_nat(1u);
v___x_2630_ = lean_nat_add(v_j_2620_, v___x_2629_);
lean_dec(v_j_2620_);
v___x_2631_ = lean_array_get_size(v_cs_2617_);
v___x_2632_ = lean_nat_dec_lt(v___x_2630_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_dec(v___x_2630_);
return v___x_2628_;
}
else
{
uint8_t v___x_2633_; 
v___x_2633_ = lean_nat_dec_le(v___x_2631_, v___x_2631_);
if (v___x_2633_ == 0)
{
if (v___x_2632_ == 0)
{
lean_dec(v___x_2630_);
return v___x_2628_;
}
else
{
size_t v___x_2634_; size_t v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = lean_usize_of_nat(v___x_2630_);
lean_dec(v___x_2630_);
v___x_2635_ = lean_usize_of_nat(v___x_2631_);
v___x_2636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_2617_, v___x_2634_, v___x_2635_, v___x_2628_);
return v___x_2636_;
}
}
else
{
size_t v___x_2637_; size_t v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = lean_usize_of_nat(v___x_2630_);
lean_dec(v___x_2630_);
v___x_2638_ = lean_usize_of_nat(v___x_2631_);
v___x_2639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_2617_, v___x_2637_, v___x_2638_, v___x_2628_);
return v___x_2639_;
}
}
}
else
{
lean_object* v_vs_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v_vs_2640_ = lean_ctor_get(v_x_2613_, 0);
v___x_2641_ = lean_usize_to_nat(v_x_2614_);
v___x_2642_ = lean_array_get_size(v_vs_2640_);
v___x_2643_ = lean_nat_dec_lt(v___x_2641_, v___x_2642_);
if (v___x_2643_ == 0)
{
lean_dec(v___x_2641_);
return v_x_2616_;
}
else
{
uint8_t v___x_2644_; 
v___x_2644_ = lean_nat_dec_le(v___x_2642_, v___x_2642_);
if (v___x_2644_ == 0)
{
if (v___x_2643_ == 0)
{
lean_dec(v___x_2641_);
return v_x_2616_;
}
else
{
size_t v___x_2645_; size_t v___x_2646_; lean_object* v___x_2647_; 
v___x_2645_ = lean_usize_of_nat(v___x_2641_);
lean_dec(v___x_2641_);
v___x_2646_ = lean_usize_of_nat(v___x_2642_);
v___x_2647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2640_, v___x_2645_, v___x_2646_, v_x_2616_);
return v___x_2647_;
}
}
else
{
size_t v___x_2648_; size_t v___x_2649_; lean_object* v___x_2650_; 
v___x_2648_ = lean_usize_of_nat(v___x_2641_);
lean_dec(v___x_2641_);
v___x_2649_ = lean_usize_of_nat(v___x_2642_);
v___x_2650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_2640_, v___x_2648_, v___x_2649_, v_x_2616_);
return v___x_2650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___boxed(lean_object* v_x_2651_, lean_object* v_x_2652_, lean_object* v_x_2653_, lean_object* v_x_2654_){
_start:
{
size_t v_x_92272__boxed_2655_; size_t v_x_92273__boxed_2656_; lean_object* v_res_2657_; 
v_x_92272__boxed_2655_ = lean_unbox_usize(v_x_2652_);
lean_dec(v_x_2652_);
v_x_92273__boxed_2656_ = lean_unbox_usize(v_x_2653_);
lean_dec(v_x_2653_);
v_res_2657_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v_x_2651_, v_x_92272__boxed_2655_, v_x_92273__boxed_2656_, v_x_2654_);
lean_dec_ref(v_x_2651_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(lean_object* v_t_2658_, lean_object* v_init_2659_, lean_object* v_start_2660_){
_start:
{
lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2661_ = lean_unsigned_to_nat(0u);
v___x_2662_ = lean_nat_dec_eq(v_start_2660_, v___x_2661_);
if (v___x_2662_ == 0)
{
lean_object* v_root_2663_; lean_object* v_tail_2664_; size_t v_shift_2665_; lean_object* v_tailOff_2666_; uint8_t v___x_2667_; 
v_root_2663_ = lean_ctor_get(v_t_2658_, 0);
v_tail_2664_ = lean_ctor_get(v_t_2658_, 1);
v_shift_2665_ = lean_ctor_get_usize(v_t_2658_, 4);
v_tailOff_2666_ = lean_ctor_get(v_t_2658_, 3);
v___x_2667_ = lean_nat_dec_le(v_tailOff_2666_, v_start_2660_);
if (v___x_2667_ == 0)
{
size_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v___x_2668_ = lean_usize_of_nat(v_start_2660_);
v___x_2669_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v_root_2663_, v___x_2668_, v_shift_2665_, v_init_2659_);
v___x_2670_ = lean_array_get_size(v_tail_2664_);
v___x_2671_ = lean_nat_dec_lt(v___x_2661_, v___x_2670_);
if (v___x_2671_ == 0)
{
return v___x_2669_;
}
else
{
uint8_t v___x_2672_; 
v___x_2672_ = lean_nat_dec_le(v___x_2670_, v___x_2670_);
if (v___x_2672_ == 0)
{
if (v___x_2671_ == 0)
{
return v___x_2669_;
}
else
{
size_t v___x_2673_; size_t v___x_2674_; lean_object* v___x_2675_; 
v___x_2673_ = ((size_t)0ULL);
v___x_2674_ = lean_usize_of_nat(v___x_2670_);
v___x_2675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2664_, v___x_2673_, v___x_2674_, v___x_2669_);
return v___x_2675_;
}
}
else
{
size_t v___x_2676_; size_t v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = ((size_t)0ULL);
v___x_2677_ = lean_usize_of_nat(v___x_2670_);
v___x_2678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2664_, v___x_2676_, v___x_2677_, v___x_2669_);
return v___x_2678_;
}
}
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; 
v___x_2679_ = lean_nat_sub(v_start_2660_, v_tailOff_2666_);
v___x_2680_ = lean_array_get_size(v_tail_2664_);
v___x_2681_ = lean_nat_dec_lt(v___x_2679_, v___x_2680_);
if (v___x_2681_ == 0)
{
lean_dec(v___x_2679_);
return v_init_2659_;
}
else
{
uint8_t v___x_2682_; 
v___x_2682_ = lean_nat_dec_le(v___x_2680_, v___x_2680_);
if (v___x_2682_ == 0)
{
if (v___x_2681_ == 0)
{
lean_dec(v___x_2679_);
return v_init_2659_;
}
else
{
size_t v___x_2683_; size_t v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = lean_usize_of_nat(v___x_2679_);
lean_dec(v___x_2679_);
v___x_2684_ = lean_usize_of_nat(v___x_2680_);
v___x_2685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2664_, v___x_2683_, v___x_2684_, v_init_2659_);
return v___x_2685_;
}
}
else
{
size_t v___x_2686_; size_t v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = lean_usize_of_nat(v___x_2679_);
lean_dec(v___x_2679_);
v___x_2687_ = lean_usize_of_nat(v___x_2680_);
v___x_2688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2664_, v___x_2686_, v___x_2687_, v_init_2659_);
return v___x_2688_;
}
}
}
}
else
{
lean_object* v_root_2689_; lean_object* v_tail_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v_root_2689_ = lean_ctor_get(v_t_2658_, 0);
v_tail_2690_ = lean_ctor_get(v_t_2658_, 1);
v___x_2691_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v_root_2689_, v_init_2659_);
v___x_2692_ = lean_array_get_size(v_tail_2690_);
v___x_2693_ = lean_nat_dec_lt(v___x_2661_, v___x_2692_);
if (v___x_2693_ == 0)
{
return v___x_2691_;
}
else
{
uint8_t v___x_2694_; 
v___x_2694_ = lean_nat_dec_le(v___x_2692_, v___x_2692_);
if (v___x_2694_ == 0)
{
if (v___x_2693_ == 0)
{
return v___x_2691_;
}
else
{
size_t v___x_2695_; size_t v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = ((size_t)0ULL);
v___x_2696_ = lean_usize_of_nat(v___x_2692_);
v___x_2697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2690_, v___x_2695_, v___x_2696_, v___x_2691_);
return v___x_2697_;
}
}
else
{
size_t v___x_2698_; size_t v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = ((size_t)0ULL);
v___x_2699_ = lean_usize_of_nat(v___x_2692_);
v___x_2700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_2690_, v___x_2698_, v___x_2699_, v___x_2691_);
return v___x_2700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___boxed(lean_object* v_t_2701_, lean_object* v_init_2702_, lean_object* v_start_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(v_t_2701_, v_init_2702_, v_start_2703_);
lean_dec(v_start_2703_);
lean_dec_ref(v_t_2701_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(lean_object* v_as_2705_, size_t v_i_2706_, size_t v_stop_2707_, lean_object* v_b_2708_){
_start:
{
uint8_t v___x_2709_; 
v___x_2709_ = lean_usize_dec_eq(v_i_2706_, v_stop_2707_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; size_t v___x_2713_; size_t v___x_2714_; 
v___x_2710_ = lean_array_uget_borrowed(v_as_2705_, v_i_2706_);
v___x_2711_ = l_Lean_PersistentArray_toArray___redArg(v___x_2710_);
v___x_2712_ = l_Array_append___redArg(v_b_2708_, v___x_2711_);
lean_dec_ref(v___x_2711_);
v___x_2713_ = ((size_t)1ULL);
v___x_2714_ = lean_usize_add(v_i_2706_, v___x_2713_);
v_i_2706_ = v___x_2714_;
v_b_2708_ = v___x_2712_;
goto _start;
}
else
{
return v_b_2708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23___boxed(lean_object* v_as_2716_, lean_object* v_i_2717_, lean_object* v_stop_2718_, lean_object* v_b_2719_){
_start:
{
size_t v_i_boxed_2720_; size_t v_stop_boxed_2721_; lean_object* v_res_2722_; 
v_i_boxed_2720_ = lean_unbox_usize(v_i_2717_);
lean_dec(v_i_2717_);
v_stop_boxed_2721_ = lean_unbox_usize(v_stop_2718_);
lean_dec(v_stop_2718_);
v_res_2722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_as_2716_, v_i_boxed_2720_, v_stop_boxed_2721_, v_b_2719_);
lean_dec_ref(v_as_2716_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(lean_object* v_x_2723_, lean_object* v_x_2724_){
_start:
{
if (lean_obj_tag(v_x_2723_) == 0)
{
lean_object* v_cs_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; 
v_cs_2725_ = lean_ctor_get(v_x_2723_, 0);
v___x_2726_ = lean_unsigned_to_nat(0u);
v___x_2727_ = lean_array_get_size(v_cs_2725_);
v___x_2728_ = lean_nat_dec_lt(v___x_2726_, v___x_2727_);
if (v___x_2728_ == 0)
{
return v_x_2724_;
}
else
{
uint8_t v___x_2729_; 
v___x_2729_ = lean_nat_dec_le(v___x_2727_, v___x_2727_);
if (v___x_2729_ == 0)
{
if (v___x_2728_ == 0)
{
return v_x_2724_;
}
else
{
size_t v___x_2730_; size_t v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = ((size_t)0ULL);
v___x_2731_ = lean_usize_of_nat(v___x_2727_);
v___x_2732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_2725_, v___x_2730_, v___x_2731_, v_x_2724_);
return v___x_2732_;
}
}
else
{
size_t v___x_2733_; size_t v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = ((size_t)0ULL);
v___x_2734_ = lean_usize_of_nat(v___x_2727_);
v___x_2735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_2725_, v___x_2733_, v___x_2734_, v_x_2724_);
return v___x_2735_;
}
}
}
else
{
lean_object* v_vs_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v_vs_2736_ = lean_ctor_get(v_x_2723_, 0);
v___x_2737_ = lean_unsigned_to_nat(0u);
v___x_2738_ = lean_array_get_size(v_vs_2736_);
v___x_2739_ = lean_nat_dec_lt(v___x_2737_, v___x_2738_);
if (v___x_2739_ == 0)
{
return v_x_2724_;
}
else
{
uint8_t v___x_2740_; 
v___x_2740_ = lean_nat_dec_le(v___x_2738_, v___x_2738_);
if (v___x_2740_ == 0)
{
if (v___x_2739_ == 0)
{
return v_x_2724_;
}
else
{
size_t v___x_2741_; size_t v___x_2742_; lean_object* v___x_2743_; 
v___x_2741_ = ((size_t)0ULL);
v___x_2742_ = lean_usize_of_nat(v___x_2738_);
v___x_2743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2736_, v___x_2741_, v___x_2742_, v_x_2724_);
return v___x_2743_;
}
}
else
{
size_t v___x_2744_; size_t v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = ((size_t)0ULL);
v___x_2745_ = lean_usize_of_nat(v___x_2738_);
v___x_2746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2736_, v___x_2744_, v___x_2745_, v_x_2724_);
return v___x_2746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(lean_object* v_as_2747_, size_t v_i_2748_, size_t v_stop_2749_, lean_object* v_b_2750_){
_start:
{
uint8_t v___x_2751_; 
v___x_2751_ = lean_usize_dec_eq(v_i_2748_, v_stop_2749_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; size_t v___x_2754_; size_t v___x_2755_; 
v___x_2752_ = lean_array_uget_borrowed(v_as_2747_, v_i_2748_);
v___x_2753_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v___x_2752_, v_b_2750_);
v___x_2754_ = ((size_t)1ULL);
v___x_2755_ = lean_usize_add(v_i_2748_, v___x_2754_);
v_i_2748_ = v___x_2755_;
v_b_2750_ = v___x_2753_;
goto _start;
}
else
{
return v_b_2750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30___boxed(lean_object* v_as_2757_, lean_object* v_i_2758_, lean_object* v_stop_2759_, lean_object* v_b_2760_){
_start:
{
size_t v_i_boxed_2761_; size_t v_stop_boxed_2762_; lean_object* v_res_2763_; 
v_i_boxed_2761_ = lean_unbox_usize(v_i_2758_);
lean_dec(v_i_2758_);
v_stop_boxed_2762_ = lean_unbox_usize(v_stop_2759_);
lean_dec(v_stop_2759_);
v_res_2763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_as_2757_, v_i_boxed_2761_, v_stop_boxed_2762_, v_b_2760_);
lean_dec_ref(v_as_2757_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24___boxed(lean_object* v_x_2764_, lean_object* v_x_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v_x_2764_, v_x_2765_);
lean_dec_ref(v_x_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(lean_object* v_x_2767_, size_t v_x_2768_, size_t v_x_2769_, lean_object* v_x_2770_){
_start:
{
if (lean_obj_tag(v_x_2767_) == 0)
{
lean_object* v_cs_2771_; lean_object* v___x_2772_; size_t v___x_2773_; lean_object* v_j_2774_; lean_object* v___x_2775_; size_t v___x_2776_; size_t v___x_2777_; size_t v___x_2778_; size_t v___x_2779_; size_t v___x_2780_; size_t v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v_cs_2771_ = lean_ctor_get(v_x_2767_, 0);
v___x_2772_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
v___x_2773_ = lean_usize_shift_right(v_x_2768_, v_x_2769_);
v_j_2774_ = lean_usize_to_nat(v___x_2773_);
v___x_2775_ = lean_array_get_borrowed(v___x_2772_, v_cs_2771_, v_j_2774_);
v___x_2776_ = ((size_t)1ULL);
v___x_2777_ = lean_usize_shift_left(v___x_2776_, v_x_2769_);
v___x_2778_ = lean_usize_sub(v___x_2777_, v___x_2776_);
v___x_2779_ = lean_usize_land(v_x_2768_, v___x_2778_);
v___x_2780_ = ((size_t)5ULL);
v___x_2781_ = lean_usize_sub(v_x_2769_, v___x_2780_);
v___x_2782_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v___x_2775_, v___x_2779_, v___x_2781_, v_x_2770_);
v___x_2783_ = lean_unsigned_to_nat(1u);
v___x_2784_ = lean_nat_add(v_j_2774_, v___x_2783_);
lean_dec(v_j_2774_);
v___x_2785_ = lean_array_get_size(v_cs_2771_);
v___x_2786_ = lean_nat_dec_lt(v___x_2784_, v___x_2785_);
if (v___x_2786_ == 0)
{
lean_dec(v___x_2784_);
return v___x_2782_;
}
else
{
uint8_t v___x_2787_; 
v___x_2787_ = lean_nat_dec_le(v___x_2785_, v___x_2785_);
if (v___x_2787_ == 0)
{
if (v___x_2786_ == 0)
{
lean_dec(v___x_2784_);
return v___x_2782_;
}
else
{
size_t v___x_2788_; size_t v___x_2789_; lean_object* v___x_2790_; 
v___x_2788_ = lean_usize_of_nat(v___x_2784_);
lean_dec(v___x_2784_);
v___x_2789_ = lean_usize_of_nat(v___x_2785_);
v___x_2790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_2771_, v___x_2788_, v___x_2789_, v___x_2782_);
return v___x_2790_;
}
}
else
{
size_t v___x_2791_; size_t v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = lean_usize_of_nat(v___x_2784_);
lean_dec(v___x_2784_);
v___x_2792_ = lean_usize_of_nat(v___x_2785_);
v___x_2793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_2771_, v___x_2791_, v___x_2792_, v___x_2782_);
return v___x_2793_;
}
}
}
else
{
lean_object* v_vs_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v_vs_2794_ = lean_ctor_get(v_x_2767_, 0);
v___x_2795_ = lean_usize_to_nat(v_x_2768_);
v___x_2796_ = lean_array_get_size(v_vs_2794_);
v___x_2797_ = lean_nat_dec_lt(v___x_2795_, v___x_2796_);
if (v___x_2797_ == 0)
{
lean_dec(v___x_2795_);
return v_x_2770_;
}
else
{
uint8_t v___x_2798_; 
v___x_2798_ = lean_nat_dec_le(v___x_2796_, v___x_2796_);
if (v___x_2798_ == 0)
{
if (v___x_2797_ == 0)
{
lean_dec(v___x_2795_);
return v_x_2770_;
}
else
{
size_t v___x_2799_; size_t v___x_2800_; lean_object* v___x_2801_; 
v___x_2799_ = lean_usize_of_nat(v___x_2795_);
lean_dec(v___x_2795_);
v___x_2800_ = lean_usize_of_nat(v___x_2796_);
v___x_2801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2794_, v___x_2799_, v___x_2800_, v_x_2770_);
return v___x_2801_;
}
}
else
{
size_t v___x_2802_; size_t v___x_2803_; lean_object* v___x_2804_; 
v___x_2802_ = lean_usize_of_nat(v___x_2795_);
lean_dec(v___x_2795_);
v___x_2803_ = lean_usize_of_nat(v___x_2796_);
v___x_2804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_2794_, v___x_2802_, v___x_2803_, v_x_2770_);
return v___x_2804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22___boxed(lean_object* v_x_2805_, lean_object* v_x_2806_, lean_object* v_x_2807_, lean_object* v_x_2808_){
_start:
{
size_t v_x_92496__boxed_2809_; size_t v_x_92497__boxed_2810_; lean_object* v_res_2811_; 
v_x_92496__boxed_2809_ = lean_unbox_usize(v_x_2806_);
lean_dec(v_x_2806_);
v_x_92497__boxed_2810_ = lean_unbox_usize(v_x_2807_);
lean_dec(v_x_2807_);
v_res_2811_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v_x_2805_, v_x_92496__boxed_2809_, v_x_92497__boxed_2810_, v_x_2808_);
lean_dec_ref(v_x_2805_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(lean_object* v_t_2812_, lean_object* v_init_2813_, lean_object* v_start_2814_){
_start:
{
lean_object* v___x_2815_; uint8_t v___x_2816_; 
v___x_2815_ = lean_unsigned_to_nat(0u);
v___x_2816_ = lean_nat_dec_eq(v_start_2814_, v___x_2815_);
if (v___x_2816_ == 0)
{
lean_object* v_root_2817_; lean_object* v_tail_2818_; size_t v_shift_2819_; lean_object* v_tailOff_2820_; uint8_t v___x_2821_; 
v_root_2817_ = lean_ctor_get(v_t_2812_, 0);
v_tail_2818_ = lean_ctor_get(v_t_2812_, 1);
v_shift_2819_ = lean_ctor_get_usize(v_t_2812_, 4);
v_tailOff_2820_ = lean_ctor_get(v_t_2812_, 3);
v___x_2821_ = lean_nat_dec_le(v_tailOff_2820_, v_start_2814_);
if (v___x_2821_ == 0)
{
size_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; 
v___x_2822_ = lean_usize_of_nat(v_start_2814_);
v___x_2823_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v_root_2817_, v___x_2822_, v_shift_2819_, v_init_2813_);
v___x_2824_ = lean_array_get_size(v_tail_2818_);
v___x_2825_ = lean_nat_dec_lt(v___x_2815_, v___x_2824_);
if (v___x_2825_ == 0)
{
return v___x_2823_;
}
else
{
uint8_t v___x_2826_; 
v___x_2826_ = lean_nat_dec_le(v___x_2824_, v___x_2824_);
if (v___x_2826_ == 0)
{
if (v___x_2825_ == 0)
{
return v___x_2823_;
}
else
{
size_t v___x_2827_; size_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = ((size_t)0ULL);
v___x_2828_ = lean_usize_of_nat(v___x_2824_);
v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2818_, v___x_2827_, v___x_2828_, v___x_2823_);
return v___x_2829_;
}
}
else
{
size_t v___x_2830_; size_t v___x_2831_; lean_object* v___x_2832_; 
v___x_2830_ = ((size_t)0ULL);
v___x_2831_ = lean_usize_of_nat(v___x_2824_);
v___x_2832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2818_, v___x_2830_, v___x_2831_, v___x_2823_);
return v___x_2832_;
}
}
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
v___x_2833_ = lean_nat_sub(v_start_2814_, v_tailOff_2820_);
v___x_2834_ = lean_array_get_size(v_tail_2818_);
v___x_2835_ = lean_nat_dec_lt(v___x_2833_, v___x_2834_);
if (v___x_2835_ == 0)
{
lean_dec(v___x_2833_);
return v_init_2813_;
}
else
{
uint8_t v___x_2836_; 
v___x_2836_ = lean_nat_dec_le(v___x_2834_, v___x_2834_);
if (v___x_2836_ == 0)
{
if (v___x_2835_ == 0)
{
lean_dec(v___x_2833_);
return v_init_2813_;
}
else
{
size_t v___x_2837_; size_t v___x_2838_; lean_object* v___x_2839_; 
v___x_2837_ = lean_usize_of_nat(v___x_2833_);
lean_dec(v___x_2833_);
v___x_2838_ = lean_usize_of_nat(v___x_2834_);
v___x_2839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2818_, v___x_2837_, v___x_2838_, v_init_2813_);
return v___x_2839_;
}
}
else
{
size_t v___x_2840_; size_t v___x_2841_; lean_object* v___x_2842_; 
v___x_2840_ = lean_usize_of_nat(v___x_2833_);
lean_dec(v___x_2833_);
v___x_2841_ = lean_usize_of_nat(v___x_2834_);
v___x_2842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2818_, v___x_2840_, v___x_2841_, v_init_2813_);
return v___x_2842_;
}
}
}
}
else
{
lean_object* v_root_2843_; lean_object* v_tail_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; 
v_root_2843_ = lean_ctor_get(v_t_2812_, 0);
v_tail_2844_ = lean_ctor_get(v_t_2812_, 1);
v___x_2845_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v_root_2843_, v_init_2813_);
v___x_2846_ = lean_array_get_size(v_tail_2844_);
v___x_2847_ = lean_nat_dec_lt(v___x_2815_, v___x_2846_);
if (v___x_2847_ == 0)
{
return v___x_2845_;
}
else
{
uint8_t v___x_2848_; 
v___x_2848_ = lean_nat_dec_le(v___x_2846_, v___x_2846_);
if (v___x_2848_ == 0)
{
if (v___x_2847_ == 0)
{
return v___x_2845_;
}
else
{
size_t v___x_2849_; size_t v___x_2850_; lean_object* v___x_2851_; 
v___x_2849_ = ((size_t)0ULL);
v___x_2850_ = lean_usize_of_nat(v___x_2846_);
v___x_2851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2844_, v___x_2849_, v___x_2850_, v___x_2845_);
return v___x_2851_;
}
}
else
{
size_t v___x_2852_; size_t v___x_2853_; lean_object* v___x_2854_; 
v___x_2852_ = ((size_t)0ULL);
v___x_2853_ = lean_usize_of_nat(v___x_2846_);
v___x_2854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_2844_, v___x_2852_, v___x_2853_, v___x_2845_);
return v___x_2854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(lean_object* v_t_2855_, lean_object* v_init_2856_, lean_object* v_start_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_t_2855_, v_init_2856_, v_start_2857_);
lean_dec(v_start_2857_);
lean_dec_ref(v_t_2855_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(lean_object* v___x_2859_, size_t v_sz_2860_, size_t v_i_2861_, lean_object* v_bs_2862_){
_start:
{
uint8_t v___x_2863_; 
v___x_2863_ = lean_usize_dec_lt(v_i_2861_, v_sz_2860_);
if (v___x_2863_ == 0)
{
return v_bs_2862_;
}
else
{
lean_object* v_v_2864_; lean_object* v___x_2865_; lean_object* v_bs_x27_2866_; lean_object* v___x_2867_; size_t v___x_2868_; size_t v___x_2869_; lean_object* v___x_2870_; 
v_v_2864_ = lean_array_uget(v_bs_2862_, v_i_2861_);
v___x_2865_ = lean_unsigned_to_nat(0u);
v_bs_x27_2866_ = lean_array_uset(v_bs_2862_, v_i_2861_, v___x_2865_);
v___x_2867_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_v_2864_, v___x_2859_);
v___x_2868_ = ((size_t)1ULL);
v___x_2869_ = lean_usize_add(v_i_2861_, v___x_2868_);
v___x_2870_ = lean_array_uset(v_bs_x27_2866_, v_i_2861_, v___x_2867_);
v_i_2861_ = v___x_2869_;
v_bs_2862_ = v___x_2870_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(lean_object* v___x_2872_, lean_object* v_sz_2873_, lean_object* v_i_2874_, lean_object* v_bs_2875_){
_start:
{
size_t v_sz_boxed_2876_; size_t v_i_boxed_2877_; lean_object* v_res_2878_; 
v_sz_boxed_2876_ = lean_unbox_usize(v_sz_2873_);
lean_dec(v_sz_2873_);
v_i_boxed_2877_ = lean_unbox_usize(v_i_2874_);
lean_dec(v_i_2874_);
v_res_2878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v___x_2872_, v_sz_boxed_2876_, v_i_boxed_2877_, v_bs_2875_);
lean_dec_ref(v___x_2872_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(lean_object* v___x_2879_, size_t v_sz_2880_, size_t v_i_2881_, lean_object* v_bs_2882_){
_start:
{
uint8_t v___x_2883_; 
v___x_2883_ = lean_usize_dec_lt(v_i_2881_, v_sz_2880_);
if (v___x_2883_ == 0)
{
return v_bs_2882_;
}
else
{
lean_object* v_v_2884_; lean_object* v___x_2885_; lean_object* v_bs_x27_2886_; lean_object* v___x_2887_; size_t v___x_2888_; size_t v___x_2889_; lean_object* v___x_2890_; 
v_v_2884_ = lean_array_uget(v_bs_2882_, v_i_2881_);
v___x_2885_ = lean_unsigned_to_nat(0u);
v_bs_x27_2886_ = lean_array_uset(v_bs_2882_, v_i_2881_, v___x_2885_);
v___x_2887_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_v_2884_, v___x_2879_);
v___x_2888_ = ((size_t)1ULL);
v___x_2889_ = lean_usize_add(v_i_2881_, v___x_2888_);
v___x_2890_ = lean_array_uset(v_bs_x27_2886_, v_i_2881_, v___x_2887_);
v_i_2881_ = v___x_2889_;
v_bs_2882_ = v___x_2890_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(lean_object* v___x_2892_, lean_object* v_sz_2893_, lean_object* v_i_2894_, lean_object* v_bs_2895_){
_start:
{
size_t v_sz_boxed_2896_; size_t v_i_boxed_2897_; lean_object* v_res_2898_; 
v_sz_boxed_2896_ = lean_unbox_usize(v_sz_2893_);
lean_dec(v_sz_2893_);
v_i_boxed_2897_ = lean_unbox_usize(v_i_2894_);
lean_dec(v_i_2894_);
v_res_2898_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_2892_, v_sz_boxed_2896_, v_i_boxed_2897_, v_bs_2895_);
lean_dec_ref(v___x_2892_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(lean_object* v_msgData_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; lean_object* v_env_2906_; lean_object* v___x_2907_; lean_object* v_mctx_2908_; lean_object* v_lctx_2909_; lean_object* v_options_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2905_ = lean_st_ref_get(v___y_2903_);
v_env_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc_ref(v_env_2906_);
lean_dec(v___x_2905_);
v___x_2907_ = lean_st_ref_get(v___y_2901_);
v_mctx_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc_ref(v_mctx_2908_);
lean_dec(v___x_2907_);
v_lctx_2909_ = lean_ctor_get(v___y_2900_, 2);
v_options_2910_ = lean_ctor_get(v___y_2902_, 2);
lean_inc_ref(v_options_2910_);
lean_inc_ref(v_lctx_2909_);
v___x_2911_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2911_, 0, v_env_2906_);
lean_ctor_set(v___x_2911_, 1, v_mctx_2908_);
lean_ctor_set(v___x_2911_, 2, v_lctx_2909_);
lean_ctor_set(v___x_2911_, 3, v_options_2910_);
v___x_2912_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
lean_ctor_set(v___x_2912_, 1, v_msgData_2899_);
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37___boxed(lean_object* v_msgData_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(v_msgData_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
return v_res_2920_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0(void){
_start:
{
lean_object* v___x_2921_; double v___x_2922_; 
v___x_2921_ = lean_unsigned_to_nat(0u);
v___x_2922_ = lean_float_of_nat(v___x_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(lean_object* v_cls_2926_, lean_object* v_msg_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_ref_2933_; lean_object* v___x_2934_; lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2979_; 
v_ref_2933_ = lean_ctor_get(v___y_2930_, 5);
v___x_2934_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(v_msg_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2937_ = v___x_2934_;
v_isShared_2938_ = v_isSharedCheck_2979_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2979_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v_traceState_2940_; lean_object* v_env_2941_; lean_object* v_nextMacroScope_2942_; lean_object* v_ngen_2943_; lean_object* v_auxDeclNGen_2944_; lean_object* v_cache_2945_; lean_object* v_messages_2946_; lean_object* v_infoState_2947_; lean_object* v_snapshotTasks_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2978_; 
v___x_2939_ = lean_st_ref_take(v___y_2931_);
v_traceState_2940_ = lean_ctor_get(v___x_2939_, 4);
v_env_2941_ = lean_ctor_get(v___x_2939_, 0);
v_nextMacroScope_2942_ = lean_ctor_get(v___x_2939_, 1);
v_ngen_2943_ = lean_ctor_get(v___x_2939_, 2);
v_auxDeclNGen_2944_ = lean_ctor_get(v___x_2939_, 3);
v_cache_2945_ = lean_ctor_get(v___x_2939_, 5);
v_messages_2946_ = lean_ctor_get(v___x_2939_, 6);
v_infoState_2947_ = lean_ctor_get(v___x_2939_, 7);
v_snapshotTasks_2948_ = lean_ctor_get(v___x_2939_, 8);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2950_ = v___x_2939_;
v_isShared_2951_ = v_isSharedCheck_2978_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_snapshotTasks_2948_);
lean_inc(v_infoState_2947_);
lean_inc(v_messages_2946_);
lean_inc(v_cache_2945_);
lean_inc(v_traceState_2940_);
lean_inc(v_auxDeclNGen_2944_);
lean_inc(v_ngen_2943_);
lean_inc(v_nextMacroScope_2942_);
lean_inc(v_env_2941_);
lean_dec(v___x_2939_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2978_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
uint64_t v_tid_2952_; lean_object* v_traces_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2977_; 
v_tid_2952_ = lean_ctor_get_uint64(v_traceState_2940_, sizeof(void*)*1);
v_traces_2953_ = lean_ctor_get(v_traceState_2940_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_traceState_2940_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2955_ = v_traceState_2940_;
v_isShared_2956_ = v_isSharedCheck_2977_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_traces_2953_);
lean_dec(v_traceState_2940_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2977_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; double v___x_2958_; uint8_t v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2957_ = lean_box(0);
v___x_2958_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0);
v___x_2959_ = 0;
v___x_2960_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1));
v___x_2961_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2961_, 0, v_cls_2926_);
lean_ctor_set(v___x_2961_, 1, v___x_2957_);
lean_ctor_set(v___x_2961_, 2, v___x_2960_);
lean_ctor_set_float(v___x_2961_, sizeof(void*)*3, v___x_2958_);
lean_ctor_set_float(v___x_2961_, sizeof(void*)*3 + 8, v___x_2958_);
lean_ctor_set_uint8(v___x_2961_, sizeof(void*)*3 + 16, v___x_2959_);
v___x_2962_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2));
v___x_2963_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set(v___x_2963_, 1, v_a_2935_);
lean_ctor_set(v___x_2963_, 2, v___x_2962_);
lean_inc(v_ref_2933_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v_ref_2933_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = l_Lean_PersistentArray_push___redArg(v_traces_2953_, v___x_2964_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2965_);
v___x_2967_ = v___x_2955_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2965_);
lean_ctor_set_uint64(v_reuseFailAlloc_2976_, sizeof(void*)*1, v_tid_2952_);
v___x_2967_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2969_; 
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 4, v___x_2967_);
v___x_2969_ = v___x_2950_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_env_2941_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_nextMacroScope_2942_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v_ngen_2943_);
lean_ctor_set(v_reuseFailAlloc_2975_, 3, v_auxDeclNGen_2944_);
lean_ctor_set(v_reuseFailAlloc_2975_, 4, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_2975_, 5, v_cache_2945_);
lean_ctor_set(v_reuseFailAlloc_2975_, 6, v_messages_2946_);
lean_ctor_set(v_reuseFailAlloc_2975_, 7, v_infoState_2947_);
lean_ctor_set(v_reuseFailAlloc_2975_, 8, v_snapshotTasks_2948_);
v___x_2969_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2970_ = lean_st_ref_set(v___y_2931_, v___x_2969_);
v___x_2971_ = lean_box(0);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 0, v___x_2971_);
v___x_2973_ = v___x_2937_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___boxed(lean_object* v_cls_2980_, lean_object* v_msg_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v_cls_2980_, v_msg_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(lean_object* v___x_2988_, size_t v_sz_2989_, size_t v_i_2990_, lean_object* v_bs_2991_){
_start:
{
uint8_t v___x_2992_; 
v___x_2992_ = lean_usize_dec_lt(v_i_2990_, v_sz_2989_);
if (v___x_2992_ == 0)
{
return v_bs_2991_;
}
else
{
lean_object* v_v_2993_; lean_object* v___x_2994_; lean_object* v_bs_x27_2995_; lean_object* v___x_2996_; size_t v___x_2997_; size_t v___x_2998_; lean_object* v___x_2999_; 
v_v_2993_ = lean_array_uget(v_bs_2991_, v_i_2990_);
v___x_2994_ = lean_unsigned_to_nat(0u);
v_bs_x27_2995_ = lean_array_uset(v_bs_2991_, v_i_2990_, v___x_2994_);
v___x_2996_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_v_2993_, v___x_2988_);
v___x_2997_ = ((size_t)1ULL);
v___x_2998_ = lean_usize_add(v_i_2990_, v___x_2997_);
v___x_2999_ = lean_array_uset(v_bs_x27_2995_, v_i_2990_, v___x_2996_);
v_i_2990_ = v___x_2998_;
v_bs_2991_ = v___x_2999_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(lean_object* v___x_3001_, lean_object* v_sz_3002_, lean_object* v_i_3003_, lean_object* v_bs_3004_){
_start:
{
size_t v_sz_boxed_3005_; size_t v_i_boxed_3006_; lean_object* v_res_3007_; 
v_sz_boxed_3005_ = lean_unbox_usize(v_sz_3002_);
lean_dec(v_sz_3002_);
v_i_boxed_3006_ = lean_unbox_usize(v_i_3003_);
lean_dec(v_i_3003_);
v_res_3007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v___x_3001_, v_sz_boxed_3005_, v_i_boxed_3006_, v_bs_3004_);
lean_dec_ref(v___x_3001_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(lean_object* v_as_3008_, size_t v_sz_3009_, size_t v_i_3010_, lean_object* v_b_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
uint8_t v___x_3023_; 
v___x_3023_ = lean_usize_dec_lt(v_i_3010_, v_sz_3009_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
v___x_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3024_, 0, v_b_3011_);
return v___x_3024_;
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3026_; 
v_a_3025_ = lean_array_uget_borrowed(v_as_3008_, v_i_3010_);
lean_inc(v_a_3025_);
v___x_3026_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(v_a_3025_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v___x_3027_; size_t v___x_3028_; size_t v___x_3029_; 
lean_dec_ref_known(v___x_3026_, 1);
v___x_3027_ = lean_box(0);
v___x_3028_ = ((size_t)1ULL);
v___x_3029_ = lean_usize_add(v_i_3010_, v___x_3028_);
v_i_3010_ = v___x_3029_;
v_b_3011_ = v___x_3027_;
goto _start;
}
else
{
return v___x_3026_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(lean_object* v_as_3031_, lean_object* v_sz_3032_, lean_object* v_i_3033_, lean_object* v_b_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
size_t v_sz_boxed_3046_; size_t v_i_boxed_3047_; lean_object* v_res_3048_; 
v_sz_boxed_3046_ = lean_unbox_usize(v_sz_3032_);
lean_dec(v_sz_3032_);
v_i_boxed_3047_ = lean_unbox_usize(v_i_3033_);
lean_dec(v_i_3033_);
v_res_3048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v_as_3031_, v_sz_boxed_3046_, v_i_boxed_3047_, v_b_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v_as_3031_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(lean_object* v_as_3049_, size_t v_sz_3050_, size_t v_i_3051_, lean_object* v_b_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
uint8_t v___x_3064_; 
v___x_3064_ = lean_usize_dec_lt(v_i_3051_, v_sz_3050_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3065_, 0, v_b_3052_);
return v___x_3065_;
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3067_; 
v_a_3066_ = lean_array_uget_borrowed(v_as_3049_, v_i_3051_);
lean_inc(v___y_3062_);
lean_inc_ref(v___y_3061_);
lean_inc(v___y_3060_);
lean_inc_ref(v___y_3059_);
lean_inc(v___y_3058_);
lean_inc_ref(v___y_3057_);
lean_inc(v___y_3056_);
lean_inc_ref(v___y_3055_);
lean_inc(v___y_3054_);
lean_inc(v___y_3053_);
lean_inc(v_a_3066_);
v___x_3067_ = lean_grind_cutsat_assert_le(v_a_3066_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v___x_3068_; size_t v___x_3069_; size_t v___x_3070_; 
lean_dec_ref_known(v___x_3067_, 1);
v___x_3068_ = lean_box(0);
v___x_3069_ = ((size_t)1ULL);
v___x_3070_ = lean_usize_add(v_i_3051_, v___x_3069_);
v_i_3051_ = v___x_3070_;
v_b_3052_ = v___x_3068_;
goto _start;
}
else
{
return v___x_3067_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(lean_object* v_as_3072_, lean_object* v_sz_3073_, lean_object* v_i_3074_, lean_object* v_b_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
size_t v_sz_boxed_3087_; size_t v_i_boxed_3088_; lean_object* v_res_3089_; 
v_sz_boxed_3087_ = lean_unbox_usize(v_sz_3073_);
lean_dec(v_sz_3073_);
v_i_boxed_3088_ = lean_unbox_usize(v_i_3074_);
lean_dec(v_i_3074_);
v_res_3089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v_as_3072_, v_sz_boxed_3087_, v_i_boxed_3088_, v_b_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v_as_3072_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
if (lean_obj_tag(v_a_3090_) == 0)
{
lean_object* v___x_3092_; 
v___x_3092_ = l_List_reverse___redArg(v_a_3091_);
return v___x_3092_;
}
else
{
lean_object* v_head_3093_; lean_object* v_tail_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3105_; 
v_head_3093_ = lean_ctor_get(v_a_3090_, 0);
v_tail_3094_ = lean_ctor_get(v_a_3090_, 1);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_a_3090_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3096_ = v_a_3090_;
v_isShared_3097_ = v_isSharedCheck_3105_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_tail_3094_);
lean_inc(v_head_3093_);
lean_dec(v_a_3090_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3105_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
v___x_3098_ = l_Nat_reprFast(v_head_3093_);
v___x_3099_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
v___x_3100_ = l_Lean_MessageData_ofFormat(v___x_3099_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 1, v_a_3091_);
lean_ctor_set(v___x_3096_, 0, v___x_3100_);
v___x_3102_ = v___x_3096_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_a_3091_);
v___x_3102_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
v_a_3090_ = v_tail_3094_;
v_a_3091_ = v___x_3102_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(lean_object* v_as_3106_, size_t v_sz_3107_, size_t v_i_3108_, lean_object* v_b_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
uint8_t v___x_3121_; 
v___x_3121_ = lean_usize_dec_lt(v_i_3108_, v_sz_3107_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; 
v___x_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3122_, 0, v_b_3109_);
return v___x_3122_;
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3124_; 
v_a_3123_ = lean_array_uget_borrowed(v_as_3106_, v_i_3108_);
lean_inc_ref(v___y_3118_);
lean_inc(v_a_3123_);
v___x_3124_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_a_3123_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v___x_3125_; size_t v___x_3126_; size_t v___x_3127_; 
lean_dec_ref_known(v___x_3124_, 1);
v___x_3125_ = lean_box(0);
v___x_3126_ = ((size_t)1ULL);
v___x_3127_ = lean_usize_add(v_i_3108_, v___x_3126_);
v_i_3108_ = v___x_3127_;
v_b_3109_ = v___x_3125_;
goto _start;
}
else
{
return v___x_3124_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(lean_object* v_as_3129_, lean_object* v_sz_3130_, lean_object* v_i_3131_, lean_object* v_b_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
size_t v_sz_boxed_3144_; size_t v_i_boxed_3145_; lean_object* v_res_3146_; 
v_sz_boxed_3144_ = lean_unbox_usize(v_sz_3130_);
lean_dec(v_sz_3130_);
v_i_boxed_3145_ = lean_unbox_usize(v_i_3131_);
lean_dec(v_i_3131_);
v_res_3146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v_as_3129_, v_sz_boxed_3144_, v_i_boxed_3145_, v_b_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v_as_3129_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(lean_object* v_as_3147_, size_t v_i_3148_, size_t v_stop_3149_, lean_object* v_b_3150_){
_start:
{
uint8_t v___x_3151_; 
v___x_3151_ = lean_usize_dec_eq(v_i_3148_, v_stop_3149_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; size_t v___x_3155_; size_t v___x_3156_; 
v___x_3152_ = lean_array_uget_borrowed(v_as_3147_, v_i_3148_);
v___x_3153_ = l_Lean_PersistentArray_toArray___redArg(v___x_3152_);
v___x_3154_ = l_Array_append___redArg(v_b_3150_, v___x_3153_);
lean_dec_ref(v___x_3153_);
v___x_3155_ = ((size_t)1ULL);
v___x_3156_ = lean_usize_add(v_i_3148_, v___x_3155_);
v_i_3148_ = v___x_3156_;
v_b_3150_ = v___x_3154_;
goto _start;
}
else
{
return v_b_3150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27___boxed(lean_object* v_as_3158_, lean_object* v_i_3159_, lean_object* v_stop_3160_, lean_object* v_b_3161_){
_start:
{
size_t v_i_boxed_3162_; size_t v_stop_boxed_3163_; lean_object* v_res_3164_; 
v_i_boxed_3162_ = lean_unbox_usize(v_i_3159_);
lean_dec(v_i_3159_);
v_stop_boxed_3163_ = lean_unbox_usize(v_stop_3160_);
lean_dec(v_stop_3160_);
v_res_3164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_as_3158_, v_i_boxed_3162_, v_stop_boxed_3163_, v_b_3161_);
lean_dec_ref(v_as_3158_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(lean_object* v_x_3165_, lean_object* v_x_3166_){
_start:
{
if (lean_obj_tag(v_x_3165_) == 0)
{
lean_object* v_cs_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; uint8_t v___x_3170_; 
v_cs_3167_ = lean_ctor_get(v_x_3165_, 0);
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = lean_array_get_size(v_cs_3167_);
v___x_3170_ = lean_nat_dec_lt(v___x_3168_, v___x_3169_);
if (v___x_3170_ == 0)
{
return v_x_3166_;
}
else
{
uint8_t v___x_3171_; 
v___x_3171_ = lean_nat_dec_le(v___x_3169_, v___x_3169_);
if (v___x_3171_ == 0)
{
if (v___x_3170_ == 0)
{
return v_x_3166_;
}
else
{
size_t v___x_3172_; size_t v___x_3173_; lean_object* v___x_3174_; 
v___x_3172_ = ((size_t)0ULL);
v___x_3173_ = lean_usize_of_nat(v___x_3169_);
v___x_3174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_3167_, v___x_3172_, v___x_3173_, v_x_3166_);
return v___x_3174_;
}
}
else
{
size_t v___x_3175_; size_t v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = ((size_t)0ULL);
v___x_3176_ = lean_usize_of_nat(v___x_3169_);
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_3167_, v___x_3175_, v___x_3176_, v_x_3166_);
return v___x_3177_;
}
}
}
else
{
lean_object* v_vs_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; uint8_t v___x_3181_; 
v_vs_3178_ = lean_ctor_get(v_x_3165_, 0);
v___x_3179_ = lean_unsigned_to_nat(0u);
v___x_3180_ = lean_array_get_size(v_vs_3178_);
v___x_3181_ = lean_nat_dec_lt(v___x_3179_, v___x_3180_);
if (v___x_3181_ == 0)
{
return v_x_3166_;
}
else
{
uint8_t v___x_3182_; 
v___x_3182_ = lean_nat_dec_le(v___x_3180_, v___x_3180_);
if (v___x_3182_ == 0)
{
if (v___x_3181_ == 0)
{
return v_x_3166_;
}
else
{
size_t v___x_3183_; size_t v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = ((size_t)0ULL);
v___x_3184_ = lean_usize_of_nat(v___x_3180_);
v___x_3185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3178_, v___x_3183_, v___x_3184_, v_x_3166_);
return v___x_3185_;
}
}
else
{
size_t v___x_3186_; size_t v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = ((size_t)0ULL);
v___x_3187_ = lean_usize_of_nat(v___x_3180_);
v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3178_, v___x_3186_, v___x_3187_, v_x_3166_);
return v___x_3188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(lean_object* v_as_3189_, size_t v_i_3190_, size_t v_stop_3191_, lean_object* v_b_3192_){
_start:
{
uint8_t v___x_3193_; 
v___x_3193_ = lean_usize_dec_eq(v_i_3190_, v_stop_3191_);
if (v___x_3193_ == 0)
{
lean_object* v___x_3194_; lean_object* v___x_3195_; size_t v___x_3196_; size_t v___x_3197_; 
v___x_3194_ = lean_array_uget_borrowed(v_as_3189_, v_i_3190_);
v___x_3195_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v___x_3194_, v_b_3192_);
v___x_3196_ = ((size_t)1ULL);
v___x_3197_ = lean_usize_add(v_i_3190_, v___x_3196_);
v_i_3190_ = v___x_3197_;
v_b_3192_ = v___x_3195_;
goto _start;
}
else
{
return v_b_3192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35___boxed(lean_object* v_as_3199_, lean_object* v_i_3200_, lean_object* v_stop_3201_, lean_object* v_b_3202_){
_start:
{
size_t v_i_boxed_3203_; size_t v_stop_boxed_3204_; lean_object* v_res_3205_; 
v_i_boxed_3203_ = lean_unbox_usize(v_i_3200_);
lean_dec(v_i_3200_);
v_stop_boxed_3204_ = lean_unbox_usize(v_stop_3201_);
lean_dec(v_stop_3201_);
v_res_3205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_as_3199_, v_i_boxed_3203_, v_stop_boxed_3204_, v_b_3202_);
lean_dec_ref(v_as_3199_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28___boxed(lean_object* v_x_3206_, lean_object* v_x_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v_x_3206_, v_x_3207_);
lean_dec_ref(v_x_3206_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(lean_object* v_x_3209_, size_t v_x_3210_, size_t v_x_3211_, lean_object* v_x_3212_){
_start:
{
if (lean_obj_tag(v_x_3209_) == 0)
{
lean_object* v_cs_3213_; lean_object* v___x_3214_; size_t v___x_3215_; lean_object* v_j_3216_; lean_object* v___x_3217_; size_t v___x_3218_; size_t v___x_3219_; size_t v___x_3220_; size_t v___x_3221_; size_t v___x_3222_; size_t v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v_cs_3213_ = lean_ctor_get(v_x_3209_, 0);
v___x_3214_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
v___x_3215_ = lean_usize_shift_right(v_x_3210_, v_x_3211_);
v_j_3216_ = lean_usize_to_nat(v___x_3215_);
v___x_3217_ = lean_array_get_borrowed(v___x_3214_, v_cs_3213_, v_j_3216_);
v___x_3218_ = ((size_t)1ULL);
v___x_3219_ = lean_usize_shift_left(v___x_3218_, v_x_3211_);
v___x_3220_ = lean_usize_sub(v___x_3219_, v___x_3218_);
v___x_3221_ = lean_usize_land(v_x_3210_, v___x_3220_);
v___x_3222_ = ((size_t)5ULL);
v___x_3223_ = lean_usize_sub(v_x_3211_, v___x_3222_);
v___x_3224_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v___x_3217_, v___x_3221_, v___x_3223_, v_x_3212_);
v___x_3225_ = lean_unsigned_to_nat(1u);
v___x_3226_ = lean_nat_add(v_j_3216_, v___x_3225_);
lean_dec(v_j_3216_);
v___x_3227_ = lean_array_get_size(v_cs_3213_);
v___x_3228_ = lean_nat_dec_lt(v___x_3226_, v___x_3227_);
if (v___x_3228_ == 0)
{
lean_dec(v___x_3226_);
return v___x_3224_;
}
else
{
uint8_t v___x_3229_; 
v___x_3229_ = lean_nat_dec_le(v___x_3227_, v___x_3227_);
if (v___x_3229_ == 0)
{
if (v___x_3228_ == 0)
{
lean_dec(v___x_3226_);
return v___x_3224_;
}
else
{
size_t v___x_3230_; size_t v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = lean_usize_of_nat(v___x_3226_);
lean_dec(v___x_3226_);
v___x_3231_ = lean_usize_of_nat(v___x_3227_);
v___x_3232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_3213_, v___x_3230_, v___x_3231_, v___x_3224_);
return v___x_3232_;
}
}
else
{
size_t v___x_3233_; size_t v___x_3234_; lean_object* v___x_3235_; 
v___x_3233_ = lean_usize_of_nat(v___x_3226_);
lean_dec(v___x_3226_);
v___x_3234_ = lean_usize_of_nat(v___x_3227_);
v___x_3235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_3213_, v___x_3233_, v___x_3234_, v___x_3224_);
return v___x_3235_;
}
}
}
else
{
lean_object* v_vs_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
v_vs_3236_ = lean_ctor_get(v_x_3209_, 0);
v___x_3237_ = lean_usize_to_nat(v_x_3210_);
v___x_3238_ = lean_array_get_size(v_vs_3236_);
v___x_3239_ = lean_nat_dec_lt(v___x_3237_, v___x_3238_);
if (v___x_3239_ == 0)
{
lean_dec(v___x_3237_);
return v_x_3212_;
}
else
{
uint8_t v___x_3240_; 
v___x_3240_ = lean_nat_dec_le(v___x_3238_, v___x_3238_);
if (v___x_3240_ == 0)
{
if (v___x_3239_ == 0)
{
lean_dec(v___x_3237_);
return v_x_3212_;
}
else
{
size_t v___x_3241_; size_t v___x_3242_; lean_object* v___x_3243_; 
v___x_3241_ = lean_usize_of_nat(v___x_3237_);
lean_dec(v___x_3237_);
v___x_3242_ = lean_usize_of_nat(v___x_3238_);
v___x_3243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3236_, v___x_3241_, v___x_3242_, v_x_3212_);
return v___x_3243_;
}
}
else
{
size_t v___x_3244_; size_t v___x_3245_; lean_object* v___x_3246_; 
v___x_3244_ = lean_usize_of_nat(v___x_3237_);
lean_dec(v___x_3237_);
v___x_3245_ = lean_usize_of_nat(v___x_3238_);
v___x_3246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_3236_, v___x_3244_, v___x_3245_, v_x_3212_);
return v___x_3246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26___boxed(lean_object* v_x_3247_, lean_object* v_x_3248_, lean_object* v_x_3249_, lean_object* v_x_3250_){
_start:
{
size_t v_x_93075__boxed_3251_; size_t v_x_93076__boxed_3252_; lean_object* v_res_3253_; 
v_x_93075__boxed_3251_ = lean_unbox_usize(v_x_3248_);
lean_dec(v_x_3248_);
v_x_93076__boxed_3252_ = lean_unbox_usize(v_x_3249_);
lean_dec(v_x_3249_);
v_res_3253_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v_x_3247_, v_x_93075__boxed_3251_, v_x_93076__boxed_3252_, v_x_3250_);
lean_dec_ref(v_x_3247_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(lean_object* v_t_3254_, lean_object* v_init_3255_, lean_object* v_start_3256_){
_start:
{
lean_object* v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = lean_unsigned_to_nat(0u);
v___x_3258_ = lean_nat_dec_eq(v_start_3256_, v___x_3257_);
if (v___x_3258_ == 0)
{
lean_object* v_root_3259_; lean_object* v_tail_3260_; size_t v_shift_3261_; lean_object* v_tailOff_3262_; uint8_t v___x_3263_; 
v_root_3259_ = lean_ctor_get(v_t_3254_, 0);
v_tail_3260_ = lean_ctor_get(v_t_3254_, 1);
v_shift_3261_ = lean_ctor_get_usize(v_t_3254_, 4);
v_tailOff_3262_ = lean_ctor_get(v_t_3254_, 3);
v___x_3263_ = lean_nat_dec_le(v_tailOff_3262_, v_start_3256_);
if (v___x_3263_ == 0)
{
size_t v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3264_ = lean_usize_of_nat(v_start_3256_);
v___x_3265_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v_root_3259_, v___x_3264_, v_shift_3261_, v_init_3255_);
v___x_3266_ = lean_array_get_size(v_tail_3260_);
v___x_3267_ = lean_nat_dec_lt(v___x_3257_, v___x_3266_);
if (v___x_3267_ == 0)
{
return v___x_3265_;
}
else
{
uint8_t v___x_3268_; 
v___x_3268_ = lean_nat_dec_le(v___x_3266_, v___x_3266_);
if (v___x_3268_ == 0)
{
if (v___x_3267_ == 0)
{
return v___x_3265_;
}
else
{
size_t v___x_3269_; size_t v___x_3270_; lean_object* v___x_3271_; 
v___x_3269_ = ((size_t)0ULL);
v___x_3270_ = lean_usize_of_nat(v___x_3266_);
v___x_3271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3260_, v___x_3269_, v___x_3270_, v___x_3265_);
return v___x_3271_;
}
}
else
{
size_t v___x_3272_; size_t v___x_3273_; lean_object* v___x_3274_; 
v___x_3272_ = ((size_t)0ULL);
v___x_3273_ = lean_usize_of_nat(v___x_3266_);
v___x_3274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3260_, v___x_3272_, v___x_3273_, v___x_3265_);
return v___x_3274_;
}
}
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3275_ = lean_nat_sub(v_start_3256_, v_tailOff_3262_);
v___x_3276_ = lean_array_get_size(v_tail_3260_);
v___x_3277_ = lean_nat_dec_lt(v___x_3275_, v___x_3276_);
if (v___x_3277_ == 0)
{
lean_dec(v___x_3275_);
return v_init_3255_;
}
else
{
uint8_t v___x_3278_; 
v___x_3278_ = lean_nat_dec_le(v___x_3276_, v___x_3276_);
if (v___x_3278_ == 0)
{
if (v___x_3277_ == 0)
{
lean_dec(v___x_3275_);
return v_init_3255_;
}
else
{
size_t v___x_3279_; size_t v___x_3280_; lean_object* v___x_3281_; 
v___x_3279_ = lean_usize_of_nat(v___x_3275_);
lean_dec(v___x_3275_);
v___x_3280_ = lean_usize_of_nat(v___x_3276_);
v___x_3281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3260_, v___x_3279_, v___x_3280_, v_init_3255_);
return v___x_3281_;
}
}
else
{
size_t v___x_3282_; size_t v___x_3283_; lean_object* v___x_3284_; 
v___x_3282_ = lean_usize_of_nat(v___x_3275_);
lean_dec(v___x_3275_);
v___x_3283_ = lean_usize_of_nat(v___x_3276_);
v___x_3284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3260_, v___x_3282_, v___x_3283_, v_init_3255_);
return v___x_3284_;
}
}
}
}
else
{
lean_object* v_root_3285_; lean_object* v_tail_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; uint8_t v___x_3289_; 
v_root_3285_ = lean_ctor_get(v_t_3254_, 0);
v_tail_3286_ = lean_ctor_get(v_t_3254_, 1);
v___x_3287_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v_root_3285_, v_init_3255_);
v___x_3288_ = lean_array_get_size(v_tail_3286_);
v___x_3289_ = lean_nat_dec_lt(v___x_3257_, v___x_3288_);
if (v___x_3289_ == 0)
{
return v___x_3287_;
}
else
{
uint8_t v___x_3290_; 
v___x_3290_ = lean_nat_dec_le(v___x_3288_, v___x_3288_);
if (v___x_3290_ == 0)
{
if (v___x_3289_ == 0)
{
return v___x_3287_;
}
else
{
size_t v___x_3291_; size_t v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = ((size_t)0ULL);
v___x_3292_ = lean_usize_of_nat(v___x_3288_);
v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3286_, v___x_3291_, v___x_3292_, v___x_3287_);
return v___x_3293_;
}
}
else
{
size_t v___x_3294_; size_t v___x_3295_; lean_object* v___x_3296_; 
v___x_3294_ = ((size_t)0ULL);
v___x_3295_ = lean_usize_of_nat(v___x_3288_);
v___x_3296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_3286_, v___x_3294_, v___x_3295_, v___x_3287_);
return v___x_3296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9___boxed(lean_object* v_t_3297_, lean_object* v_init_3298_, lean_object* v_start_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v_t_3297_, v_init_3298_, v_start_3299_);
lean_dec(v_start_3299_);
lean_dec_ref(v_t_3297_);
return v_res_3300_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6));
v___x_3318_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8));
v___x_3319_ = l_Lean_Name_append(v___x_3318_, v___x_3317_);
return v___x_3319_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10));
v___x_3322_ = l_Lean_stringToMessageData(v___x_3321_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12));
v___x_3325_ = l_Lean_stringToMessageData(v___x_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v___x_3337_; 
v___x_3337_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3326_, v_a_3334_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3432_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3432_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3432_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v_vars_3342_; lean_object* v_vars_x27_3343_; lean_object* v_dvds_3344_; lean_object* v_lowers_3345_; lean_object* v_uppers_3346_; lean_object* v_diseqs_3347_; uint8_t v___x_3348_; 
v_vars_3342_ = lean_ctor_get(v_a_3338_, 0);
lean_inc_ref(v_vars_3342_);
v_vars_x27_3343_ = lean_ctor_get(v_a_3338_, 2);
lean_inc_ref(v_vars_x27_3343_);
v_dvds_3344_ = lean_ctor_get(v_a_3338_, 6);
lean_inc_ref(v_dvds_3344_);
v_lowers_3345_ = lean_ctor_get(v_a_3338_, 7);
lean_inc_ref(v_lowers_3345_);
v_uppers_3346_ = lean_ctor_get(v_a_3338_, 8);
lean_inc_ref(v_uppers_3346_);
v_diseqs_3347_ = lean_ctor_get(v_a_3338_, 9);
lean_inc_ref(v_diseqs_3347_);
lean_dec(v_a_3338_);
v___x_3348_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_3342_);
lean_dec_ref(v_vars_3342_);
if (v___x_3348_ == 0)
{
uint8_t v___x_3349_; 
v___x_3349_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_x27_3343_);
lean_dec_ref(v_vars_x27_3343_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; lean_object* v___x_3352_; 
lean_dec_ref(v_diseqs_3347_);
lean_dec_ref(v_uppers_3346_);
lean_dec_ref(v_lowers_3345_);
lean_dec_ref(v_dvds_3344_);
v___x_3350_ = lean_box(0);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3350_);
v___x_3352_ = v___x_3340_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3350_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
else
{
lean_object* v___x_3354_; 
lean_del_object(v___x_3340_);
v___x_3354_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v___x_3355_; 
lean_dec_ref_known(v___x_3354_, 1);
v___x_3355_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3357_; lean_object* v___f_3358_; lean_object* v___f_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc_n(v_a_3356_, 2);
lean_dec_ref_known(v___x_3355_, 1);
v___x_3357_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_a_3356_);
lean_inc_ref_n(v___x_3357_, 2);
v___f_3358_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3358_, 0, v___x_3357_);
v___f_3359_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3359_, 0, v_a_3356_);
lean_closure_set(v___f_3359_, 1, v___f_3358_);
lean_closure_set(v___f_3359_, 2, v___x_3357_);
v___x_3360_ = lean_unsigned_to_nat(0u);
v___x_3361_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0));
v___x_3362_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(v_dvds_3344_, v___x_3361_, v___x_3360_);
lean_dec_ref(v_dvds_3344_);
v___x_3363_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_lowers_3345_, v___x_3361_, v___x_3360_);
lean_dec_ref(v_lowers_3345_);
v___x_3364_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3365_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3364_, v___f_3359_, v_a_3326_);
if (lean_obj_tag(v___x_3365_) == 0)
{
size_t v_sz_3366_; size_t v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; size_t v_sz_3370_; lean_object* v___x_3371_; 
lean_dec_ref_known(v___x_3365_, 1);
v_sz_3366_ = lean_array_size(v___x_3362_);
v___x_3367_ = ((size_t)0ULL);
v___x_3368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v___x_3357_, v_sz_3366_, v___x_3367_, v___x_3362_);
v___x_3369_ = lean_box(0);
v_sz_3370_ = lean_array_size(v___x_3368_);
v___x_3371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_3368_, v_sz_3370_, v___x_3367_, v___x_3369_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
lean_dec_ref(v___x_3368_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v___x_3372_; size_t v_sz_3373_; lean_object* v___x_3374_; size_t v_sz_3375_; lean_object* v___x_3376_; 
lean_dec_ref_known(v___x_3371_, 1);
v___x_3372_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_uppers_3346_, v___x_3363_, v___x_3360_);
lean_dec_ref(v_uppers_3346_);
v_sz_3373_ = lean_array_size(v___x_3372_);
v___x_3374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v___x_3357_, v_sz_3373_, v___x_3367_, v___x_3372_);
v_sz_3375_ = lean_array_size(v___x_3374_);
v___x_3376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v___x_3374_, v_sz_3375_, v___x_3367_, v___x_3369_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
lean_dec_ref(v___x_3374_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v___x_3377_; size_t v_sz_3378_; lean_object* v___x_3379_; size_t v_sz_3380_; lean_object* v___x_3381_; 
lean_dec_ref_known(v___x_3376_, 1);
v___x_3377_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v_diseqs_3347_, v___x_3361_, v___x_3360_);
lean_dec_ref(v_diseqs_3347_);
v_sz_3378_ = lean_array_size(v___x_3377_);
v___x_3379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_3357_, v_sz_3378_, v___x_3367_, v___x_3377_);
v_sz_3380_ = lean_array_size(v___x_3379_);
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v___x_3379_, v_sz_3380_, v___x_3367_, v___x_3369_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
lean_dec_ref(v___x_3379_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_options_3382_; uint8_t v_hasTrace_3383_; 
lean_dec_ref_known(v___x_3381_, 1);
v_options_3382_ = lean_ctor_get(v_a_3334_, 2);
v_hasTrace_3383_ = lean_ctor_get_uint8(v_options_3382_, sizeof(void*)*1);
if (v_hasTrace_3383_ == 0)
{
lean_object* v___x_3384_; 
lean_dec_ref(v___x_3357_);
lean_dec(v_a_3356_);
v___x_3384_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
return v___x_3384_;
}
else
{
lean_object* v_inheritedTraceOptions_3385_; lean_object* v___x_3386_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v_options_3397_; lean_object* v_inheritedTraceOptions_3398_; lean_object* v___y_3399_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v_inheritedTraceOptions_3385_ = lean_ctor_get(v_a_3334_, 13);
v___x_3386_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6));
v___x_3411_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9);
v___x_3412_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3385_, v_options_3382_, v___x_3411_);
if (v___x_3412_ == 0)
{
lean_dec(v_a_3356_);
v___y_3388_ = v_a_3326_;
v___y_3389_ = v_a_3327_;
v___y_3390_ = v_a_3328_;
v___y_3391_ = v_a_3329_;
v___y_3392_ = v_a_3330_;
v___y_3393_ = v_a_3331_;
v___y_3394_ = v_a_3332_;
v___y_3395_ = v_a_3333_;
v___y_3396_ = v_a_3334_;
v_options_3397_ = v_options_3382_;
v_inheritedTraceOptions_3398_ = v_inheritedTraceOptions_3385_;
v___y_3399_ = v_a_3335_;
goto v___jp_3387_;
}
else
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3413_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13);
v___x_3414_ = lean_array_to_list(v_a_3356_);
v___x_3415_ = lean_box(0);
v___x_3416_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v___x_3414_, v___x_3415_);
v___x_3417_ = l_Lean_MessageData_ofList(v___x_3416_);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3413_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v___x_3386_, v___x_3418_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_dec_ref_known(v___x_3419_, 1);
v___y_3388_ = v_a_3326_;
v___y_3389_ = v_a_3327_;
v___y_3390_ = v_a_3328_;
v___y_3391_ = v_a_3329_;
v___y_3392_ = v_a_3330_;
v___y_3393_ = v_a_3331_;
v___y_3394_ = v_a_3332_;
v___y_3395_ = v_a_3333_;
v___y_3396_ = v_a_3334_;
v_options_3397_ = v_options_3382_;
v_inheritedTraceOptions_3398_ = v_inheritedTraceOptions_3385_;
v___y_3399_ = v_a_3335_;
goto v___jp_3387_;
}
else
{
lean_dec_ref(v___x_3357_);
return v___x_3419_;
}
}
v___jp_3387_:
{
lean_object* v___x_3400_; uint8_t v___x_3401_; 
v___x_3400_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9);
v___x_3401_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3398_, v_options_3397_, v___x_3400_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; 
lean_dec_ref(v___x_3357_);
v___x_3402_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3399_);
return v___x_3402_;
}
else
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3403_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11);
v___x_3404_ = lean_array_to_list(v___x_3357_);
v___x_3405_ = lean_box(0);
v___x_3406_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v___x_3404_, v___x_3405_);
v___x_3407_ = l_Lean_MessageData_ofList(v___x_3406_);
v___x_3408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3403_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
v___x_3409_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v___x_3386_, v___x_3408_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3399_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v___x_3410_; 
lean_dec_ref_known(v___x_3409_, 1);
v___x_3410_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3399_);
return v___x_3410_;
}
else
{
return v___x_3409_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3357_);
lean_dec(v_a_3356_);
return v___x_3381_;
}
}
else
{
lean_dec_ref(v___x_3357_);
lean_dec(v_a_3356_);
lean_dec_ref(v_diseqs_3347_);
return v___x_3376_;
}
}
else
{
lean_dec_ref(v___x_3363_);
lean_dec_ref(v___x_3357_);
lean_dec(v_a_3356_);
lean_dec_ref(v_diseqs_3347_);
lean_dec_ref(v_uppers_3346_);
return v___x_3371_;
}
}
else
{
lean_dec_ref(v___x_3363_);
lean_dec_ref(v___x_3362_);
lean_dec_ref(v___x_3357_);
lean_dec(v_a_3356_);
lean_dec_ref(v_diseqs_3347_);
lean_dec_ref(v_uppers_3346_);
return v___x_3365_;
}
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_dec_ref(v_diseqs_3347_);
lean_dec_ref(v_uppers_3346_);
lean_dec_ref(v_lowers_3345_);
lean_dec_ref(v_dvds_3344_);
v_a_3420_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3355_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3355_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
else
{
lean_dec_ref(v_diseqs_3347_);
lean_dec_ref(v_uppers_3346_);
lean_dec_ref(v_lowers_3345_);
lean_dec_ref(v_dvds_3344_);
return v___x_3354_;
}
}
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3430_; 
lean_dec_ref(v_diseqs_3347_);
lean_dec_ref(v_uppers_3346_);
lean_dec_ref(v_lowers_3345_);
lean_dec_ref(v_dvds_3344_);
lean_dec_ref(v_vars_x27_3343_);
v___x_3428_ = lean_box(0);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3428_);
v___x_3430_ = v___x_3340_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
v_a_3433_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3337_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3337_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
lean_dec(v_a_3450_);
lean_dec_ref(v_a_3449_);
lean_dec(v_a_3448_);
lean_dec_ref(v_a_3447_);
lean_dec(v_a_3446_);
lean_dec_ref(v_a_3445_);
lean_dec(v_a_3444_);
lean_dec_ref(v_a_3443_);
lean_dec(v_a_3442_);
lean_dec(v_a_3441_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(lean_object* v_00_u03b2_3453_, lean_object* v_00_u03c3_3454_, lean_object* v_pm_3455_, lean_object* v_f_3456_){
_start:
{
lean_object* v___x_3457_; 
v___x_3457_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_pm_3455_, v_f_3456_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(lean_object* v_cls_3458_, lean_object* v_msg_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v_cls_3458_, v_msg_3459_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___boxed(lean_object* v_cls_3472_, lean_object* v_msg_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(v_cls_3472_, v_msg_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec(v___y_3474_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0___redArg(lean_object* v_pm_3486_, lean_object* v_f_3487_){
_start:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_3487_, v_pm_3486_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0(lean_object* v_00_u03b2_3489_, lean_object* v_00_u03c3_3490_, lean_object* v_pm_3491_, lean_object* v_f_3492_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_3492_, v_pm_3491_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3494_, lean_object* v_00_u03b2_3495_, lean_object* v_00_u03c3_3496_, lean_object* v_f_3497_, lean_object* v_n_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_3497_, v_n_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20(lean_object* v_00_u03b1_3500_, lean_object* v_00_u03b2_3501_, lean_object* v_00_u03c3_3502_, lean_object* v_f_3503_, size_t v_sz_3504_, size_t v_i_3505_, lean_object* v_bs_3506_){
_start:
{
lean_object* v___x_3507_; 
v___x_3507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(v_f_3503_, v_sz_3504_, v_i_3505_, v_bs_3506_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___boxed(lean_object* v_00_u03b1_3508_, lean_object* v_00_u03b2_3509_, lean_object* v_00_u03c3_3510_, lean_object* v_f_3511_, lean_object* v_sz_3512_, lean_object* v_i_3513_, lean_object* v_bs_3514_){
_start:
{
size_t v_sz_boxed_3515_; size_t v_i_boxed_3516_; lean_object* v_res_3517_; 
v_sz_boxed_3515_ = lean_unbox_usize(v_sz_3512_);
lean_dec(v_sz_3512_);
v_i_boxed_3516_ = lean_unbox_usize(v_i_3513_);
lean_dec(v_i_3513_);
v_res_3517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20(v_00_u03b1_3508_, v_00_u03b2_3509_, v_00_u03c3_3510_, v_f_3511_, v_sz_boxed_3515_, v_i_boxed_3516_, v_bs_3514_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21(lean_object* v_00_u03b1_3518_, lean_object* v_00_u03b2_3519_, lean_object* v_f_3520_, lean_object* v_as_3521_){
_start:
{
lean_object* v___x_3522_; 
v___x_3522_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(v_f_3520_, v_as_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___boxed(lean_object* v_00_u03b1_3523_, lean_object* v_00_u03b2_3524_, lean_object* v_f_3525_, lean_object* v_as_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21(v_00_u03b1_3523_, v_00_u03b2_3524_, v_f_3525_, v_as_3526_);
lean_dec_ref(v_as_3526_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41(lean_object* v_00_u03b1_3528_, lean_object* v_00_u03b2_3529_, lean_object* v_f_3530_, lean_object* v_as_3531_, lean_object* v_i_3532_, lean_object* v_acc_3533_, lean_object* v_hle_3534_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(v_f_3530_, v_as_3531_, v_i_3532_, v_acc_3533_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___boxed(lean_object* v_00_u03b1_3536_, lean_object* v_00_u03b2_3537_, lean_object* v_f_3538_, lean_object* v_as_3539_, lean_object* v_i_3540_, lean_object* v_acc_3541_, lean_object* v_hle_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41(v_00_u03b1_3536_, v_00_u03b2_3537_, v_f_3538_, v_as_3539_, v_i_3540_, v_acc_3541_, v_hle_3542_);
lean_dec_ref(v_as_3539_);
return v_res_3543_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
