// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.OfNatModule
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM import Init.Grind.Module.OfNatModule import Init.Grind.Module.NatModuleNorm import Lean.Meta.Tactic.Grind.Diseq import Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr import Init.Data.Nat.Order import Init.Data.Order.Lemmas import Lean.Data.RArray
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDiseqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Expr_toPolyN(lean_object*);
uint8_t l_Lean_Grind_Linarith_instBEqPoly_beq(lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`grind` internal error, invalid natStructId"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfNatModuleM_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfNatModuleM = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfNatModuleM_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "expression in two different nat module structures in linarith module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7_value),LEAN_SCALAR_PTR_LITERAL(23, 127, 6, 115, 121, 139, 223, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IntModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNatModule"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16_value),LEAN_SCALAR_PTR_LITERAL(228, 65, 165, 57, 92, 99, 138, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "smul_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18_value),LEAN_SCALAR_PTR_LITERAL(76, 96, 205, 43, 14, 83, 20, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toQ_zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20_value),LEAN_SCALAR_PTR_LITERAL(127, 170, 123, 35, 245, 189, 60, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Linarith"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eq_normN"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(126, 34, 3, 158, 236, 88, 5, 190)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg(lean_object* v_natStructId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_apply_12(v_x_2_, v_natStructId_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg___boxed(lean_object* v_natStructId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg(v_natStructId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(lean_object* v_00_u03b1_29_, lean_object* v_natStructId_30_, lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_apply_12(v_x_31_, v_natStructId_30_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___boxed(lean_object* v_00_u03b1_44_, lean_object* v_natStructId_45_, lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(v_00_u03b1_44_, v_natStructId_45_, v_x_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_a_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg___boxed(lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(v_a_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId(lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v_a_65_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___boxed(lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId(v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec(v_a_79_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(lean_object* v_msgData_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___x_97_; lean_object* v_env_98_; lean_object* v___x_99_; lean_object* v_mctx_100_; lean_object* v_lctx_101_; lean_object* v_options_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_97_ = lean_st_ref_get(v___y_95_);
v_env_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_env_98_);
lean_dec(v___x_97_);
v___x_99_ = lean_st_ref_get(v___y_93_);
v_mctx_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc_ref(v_mctx_100_);
lean_dec(v___x_99_);
v_lctx_101_ = lean_ctor_get(v___y_92_, 2);
v_options_102_ = lean_ctor_get(v___y_94_, 2);
lean_inc_ref(v_options_102_);
lean_inc_ref(v_lctx_101_);
v___x_103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_103_, 0, v_env_98_);
lean_ctor_set(v___x_103_, 1, v_mctx_100_);
lean_ctor_set(v___x_103_, 2, v_lctx_101_);
lean_ctor_set(v___x_103_, 3, v_options_102_);
v___x_104_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v_msgData_91_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0___boxed(lean_object* v_msgData_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(v_msgData_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(lean_object* v_msg_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_ref_119_; lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_ref_119_ = lean_ctor_get(v___y_116_, 5);
v___x_120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(v_msg_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_ref_119_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v_ref_119_);
lean_ctor_set(v___x_125_, 1, v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 1);
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg___boxed(lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_136_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0));
v___x_139_ = l_Lean_stringToMessageData(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct(lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_141_, v_a_149_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_166_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_166_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_166_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_166_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v_natStructs_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_natStructs_157_ = lean_ctor_get(v_a_153_, 5);
lean_inc_ref(v_natStructs_157_);
lean_dec(v_a_153_);
v___x_158_ = lean_array_get_size(v_natStructs_157_);
v___x_159_ = lean_nat_dec_lt(v_a_140_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec_ref(v_natStructs_157_);
lean_del_object(v___x_155_);
v___x_160_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1);
v___x_161_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v___x_160_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_array_fget(v_natStructs_157_, v_a_140_);
lean_dec_ref(v_natStructs_157_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_162_);
v___x_164_ = v___x_155_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
v_a_167_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_152_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_152_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStruct___boxed(lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec(v_a_176_);
lean_dec(v_a_175_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(lean_object* v_00_u03b1_188_, lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v_msg_189_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___boxed(lean_object* v_00_u03b1_203_, lean_object* v_msg_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(v_00_u03b1_203_, v_msg_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec(v___y_206_);
lean_dec(v___y_205_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v_structId_232_; lean_object* v___x_233_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref(v___x_230_);
v_structId_232_ = lean_ctor_get(v_a_231_, 1);
lean_inc(v_structId_232_);
lean_dec(v_a_231_);
v___x_233_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_structId_232_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
lean_dec(v_structId_232_);
return v___x_233_;
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
v_a_234_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_230_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_230_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct___boxed(lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec(v_a_243_);
lean_dec(v_a_242_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(lean_object* v_a_256_, lean_object* v_f_257_, lean_object* v_s_258_){
_start:
{
lean_object* v_structs_259_; lean_object* v_typeIdOf_260_; lean_object* v_exprToStructId_261_; lean_object* v_exprToStructIdEntries_262_; lean_object* v_forbiddenNatModules_263_; lean_object* v_natStructs_264_; lean_object* v_natTypeIdOf_265_; lean_object* v_exprToNatStructId_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_structs_259_ = lean_ctor_get(v_s_258_, 0);
v_typeIdOf_260_ = lean_ctor_get(v_s_258_, 1);
v_exprToStructId_261_ = lean_ctor_get(v_s_258_, 2);
v_exprToStructIdEntries_262_ = lean_ctor_get(v_s_258_, 3);
v_forbiddenNatModules_263_ = lean_ctor_get(v_s_258_, 4);
v_natStructs_264_ = lean_ctor_get(v_s_258_, 5);
v_natTypeIdOf_265_ = lean_ctor_get(v_s_258_, 6);
v_exprToNatStructId_266_ = lean_ctor_get(v_s_258_, 7);
v___x_267_ = lean_array_get_size(v_natStructs_264_);
v___x_268_ = lean_nat_dec_lt(v_a_256_, v___x_267_);
if (v___x_268_ == 0)
{
lean_dec_ref(v_f_257_);
return v_s_258_;
}
else
{
lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_280_; 
lean_inc_ref(v_exprToNatStructId_266_);
lean_inc_ref(v_natTypeIdOf_265_);
lean_inc_ref(v_natStructs_264_);
lean_inc_ref(v_forbiddenNatModules_263_);
lean_inc_ref(v_exprToStructIdEntries_262_);
lean_inc_ref(v_exprToStructId_261_);
lean_inc_ref(v_typeIdOf_260_);
lean_inc_ref(v_structs_259_);
v_isSharedCheck_280_ = !lean_is_exclusive(v_s_258_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; lean_object* v_unused_288_; 
v_unused_281_ = lean_ctor_get(v_s_258_, 7);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_s_258_, 6);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_s_258_, 5);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v_s_258_, 4);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_s_258_, 3);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_s_258_, 2);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_s_258_, 1);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_s_258_, 0);
lean_dec(v_unused_288_);
v___x_270_ = v_s_258_;
v_isShared_271_ = v_isSharedCheck_280_;
goto v_resetjp_269_;
}
else
{
lean_dec(v_s_258_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_280_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v_v_272_; lean_object* v___x_273_; lean_object* v_xs_x27_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v_v_272_ = lean_array_fget(v_natStructs_264_, v_a_256_);
v___x_273_ = lean_box(0);
v_xs_x27_274_ = lean_array_fset(v_natStructs_264_, v_a_256_, v___x_273_);
v___x_275_ = lean_apply_1(v_f_257_, v_v_272_);
v___x_276_ = lean_array_fset(v_xs_x27_274_, v_a_256_, v___x_275_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 5, v___x_276_);
v___x_278_ = v___x_270_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_structs_259_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_typeIdOf_260_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_exprToStructId_261_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_exprToStructIdEntries_262_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_forbiddenNatModules_263_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_279_, 6, v_natTypeIdOf_265_);
lean_ctor_set(v_reuseFailAlloc_279_, 7, v_exprToNatStructId_266_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed(lean_object* v_a_289_, lean_object* v_f_290_, lean_object* v_s_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(v_a_289_, v_f_290_, v_s_291_);
lean_dec(v_a_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(lean_object* v_f_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___f_297_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_297_, 0, v_a_294_);
lean_closure_set(v___f_297_, 1, v_f_293_);
v___x_298_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_299_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_298_, v___f_297_, v_a_295_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___boxed(lean_object* v_f_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(v_f_300_, v_a_301_, v_a_302_);
lean_dec(v_a_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(lean_object* v_f_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___f_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___f_318_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_318_, 0, v_a_306_);
lean_closure_set(v___f_318_, 1, v_f_305_);
v___x_319_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_320_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_319_, v___f_318_, v_a_307_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___boxed(lean_object* v_f_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(v_f_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_335_, lean_object* v_vals_336_, lean_object* v_i_337_, lean_object* v_k_338_){
_start:
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_array_get_size(v_keys_335_);
v___x_340_ = lean_nat_dec_lt(v_i_337_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_dec(v_i_337_);
v___x_341_ = lean_box(0);
return v___x_341_;
}
else
{
lean_object* v_k_x27_342_; uint8_t v___x_343_; 
v_k_x27_342_ = lean_array_fget_borrowed(v_keys_335_, v_i_337_);
v___x_343_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_338_, v_k_x27_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = lean_nat_add(v_i_337_, v___x_344_);
lean_dec(v_i_337_);
v_i_337_ = v___x_345_;
goto _start;
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_array_fget_borrowed(v_vals_336_, v_i_337_);
lean_dec(v_i_337_);
lean_inc(v___x_347_);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_349_, lean_object* v_vals_350_, lean_object* v_i_351_, lean_object* v_k_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_349_, v_vals_350_, v_i_351_, v_k_352_);
lean_dec_ref(v_k_352_);
lean_dec_ref(v_vals_350_);
lean_dec_ref(v_keys_349_);
return v_res_353_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_354_; size_t v___x_355_; size_t v___x_356_; 
v___x_354_ = ((size_t)5ULL);
v___x_355_ = ((size_t)1ULL);
v___x_356_ = lean_usize_shift_left(v___x_355_, v___x_354_);
return v___x_356_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; 
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0);
v___x_359_ = lean_usize_sub(v___x_358_, v___x_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_360_, size_t v_x_361_, lean_object* v_x_362_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
lean_object* v_es_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_384_; 
v_es_363_ = lean_ctor_get(v_x_360_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_384_ == 0)
{
v___x_365_ = v_x_360_;
v_isShared_366_ = v_isSharedCheck_384_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_es_363_);
lean_dec(v_x_360_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_384_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; lean_object* v_j_371_; lean_object* v___x_372_; 
v___x_367_ = lean_box(2);
v___x_368_ = ((size_t)5ULL);
v___x_369_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_370_ = lean_usize_land(v_x_361_, v___x_369_);
v_j_371_ = lean_usize_to_nat(v___x_370_);
v___x_372_ = lean_array_get(v___x_367_, v_es_363_, v_j_371_);
lean_dec(v_j_371_);
lean_dec_ref(v_es_363_);
switch(lean_obj_tag(v___x_372_))
{
case 0:
{
lean_object* v_key_373_; lean_object* v_val_374_; uint8_t v___x_375_; 
v_key_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_key_373_);
v_val_374_ = lean_ctor_get(v___x_372_, 1);
lean_inc(v_val_374_);
lean_dec_ref(v___x_372_);
v___x_375_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_362_, v_key_373_);
lean_dec(v_key_373_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_dec(v_val_374_);
lean_del_object(v___x_365_);
v___x_376_ = lean_box(0);
return v___x_376_;
}
else
{
lean_object* v___x_378_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 1);
lean_ctor_set(v___x_365_, 0, v_val_374_);
v___x_378_ = v___x_365_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_val_374_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
case 1:
{
lean_object* v_node_380_; size_t v___x_381_; 
lean_del_object(v___x_365_);
v_node_380_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_node_380_);
lean_dec_ref(v___x_372_);
v___x_381_ = lean_usize_shift_right(v_x_361_, v___x_368_);
v_x_360_ = v_node_380_;
v_x_361_ = v___x_381_;
goto _start;
}
default: 
{
lean_object* v___x_383_; 
lean_del_object(v___x_365_);
v___x_383_ = lean_box(0);
return v___x_383_;
}
}
}
}
else
{
lean_object* v_ks_385_; lean_object* v_vs_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_ks_385_ = lean_ctor_get(v_x_360_, 0);
lean_inc_ref(v_ks_385_);
v_vs_386_ = lean_ctor_get(v_x_360_, 1);
lean_inc_ref(v_vs_386_);
lean_dec_ref(v_x_360_);
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_385_, v_vs_386_, v___x_387_, v_x_362_);
lean_dec_ref(v_vs_386_);
lean_dec_ref(v_ks_385_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_389_, lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
size_t v_x_960__boxed_392_; lean_object* v_res_393_; 
v_x_960__boxed_392_ = lean_unbox_usize(v_x_390_);
lean_dec(v_x_390_);
v_res_393_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_389_, v_x_960__boxed_392_, v_x_391_);
lean_dec_ref(v_x_391_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
uint64_t v___x_396_; size_t v___x_397_; lean_object* v___x_398_; 
v___x_396_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_395_);
v___x_397_ = lean_uint64_to_usize(v___x_396_);
v___x_398_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_394_, v___x_397_, v_x_395_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_x_399_, v_x_400_);
lean_dec_ref(v_x_400_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(lean_object* v_e_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_416_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_416_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_exprToNatStructId_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v_exprToNatStructId_411_ = lean_ctor_get(v_a_407_, 7);
lean_inc_ref(v_exprToNatStructId_411_);
lean_dec(v_a_407_);
v___x_412_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_exprToNatStructId_411_, v_e_402_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_412_);
v___x_414_ = v___x_409_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
v_a_417_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_406_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_406_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg___boxed(lean_object* v_e_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_425_, v_a_426_, v_a_427_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_e_425_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(lean_object* v_e_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_430_, v_a_431_, v_a_439_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___boxed(lean_object* v_e_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(v_e_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_e_443_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(lean_object* v_00_u03b2_456_, lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_x_457_, v_x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_460_, lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(v_00_u03b2_460_, v_x_461_, v_x_462_);
lean_dec_ref(v_x_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_464_, lean_object* v_x_465_, size_t v_x_466_, lean_object* v_x_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_465_, v_x_466_, v_x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_469_, lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
size_t v_x_1125__boxed_473_; lean_object* v_res_474_; 
v_x_1125__boxed_473_ = lean_unbox_usize(v_x_471_);
lean_dec(v_x_471_);
v_res_474_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(v_00_u03b2_469_, v_x_470_, v_x_1125__boxed_473_, v_x_472_);
lean_dec_ref(v_x_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_475_, lean_object* v_keys_476_, lean_object* v_vals_477_, lean_object* v_heq_478_, lean_object* v_i_479_, lean_object* v_k_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_476_, v_vals_477_, v_i_479_, v_k_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_482_, lean_object* v_keys_483_, lean_object* v_vals_484_, lean_object* v_heq_485_, lean_object* v_i_486_, lean_object* v_k_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_482_, v_keys_483_, v_vals_484_, v_heq_485_, v_i_486_, v_k_487_);
lean_dec_ref(v_k_487_);
lean_dec_ref(v_vals_484_);
lean_dec_ref(v_keys_483_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(lean_object* v_a_489_, lean_object* v_b_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_a_489_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_523_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_523_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_523_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_523_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
if (lean_obj_tag(v_a_495_) == 1)
{
lean_object* v_val_499_; lean_object* v___x_500_; 
lean_del_object(v___x_497_);
v_val_499_ = lean_ctor_get(v_a_495_, 0);
v___x_500_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_b_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_518_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_518_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_518_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_518_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
if (lean_obj_tag(v_a_501_) == 1)
{
lean_object* v_val_505_; uint8_t v___x_506_; 
v_val_505_ = lean_ctor_get(v_a_501_, 0);
lean_inc(v_val_505_);
lean_dec_ref(v_a_501_);
v___x_506_ = lean_nat_dec_eq(v_val_499_, v_val_505_);
lean_dec(v_val_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_509_; 
lean_dec_ref(v_a_495_);
v___x_507_ = lean_box(0);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_507_);
v___x_509_ = v___x_503_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
else
{
lean_object* v___x_512_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v_a_495_);
v___x_512_ = v___x_503_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_495_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_516_; 
lean_dec(v_a_501_);
lean_dec_ref(v_a_495_);
v___x_514_ = lean_box(0);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_514_);
v___x_516_ = v___x_503_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
lean_dec_ref(v_a_495_);
return v___x_500_;
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_521_; 
lean_dec(v_a_495_);
v___x_519_ = lean_box(0);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_519_);
v___x_521_ = v___x_497_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg___boxed(lean_object* v_a_524_, lean_object* v_b_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_524_, v_b_525_, v_a_526_, v_a_527_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_b_525_);
lean_dec_ref(v_a_524_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(lean_object* v_a_530_, lean_object* v_b_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(v_a_530_, v_b_531_, v_a_532_, v_a_540_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___boxed(lean_object* v_a_544_, lean_object* v_b_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(v_a_544_, v_b_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_b_545_);
lean_dec_ref(v_a_544_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
lean_object* v_ks_562_; lean_object* v_vs_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_587_; 
v_ks_562_ = lean_ctor_get(v_x_558_, 0);
v_vs_563_ = lean_ctor_get(v_x_558_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_x_558_);
if (v_isSharedCheck_587_ == 0)
{
v___x_565_ = v_x_558_;
v_isShared_566_ = v_isSharedCheck_587_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_vs_563_);
lean_inc(v_ks_562_);
lean_dec(v_x_558_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_587_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_567_ = lean_array_get_size(v_ks_562_);
v___x_568_ = lean_nat_dec_lt(v_x_559_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
lean_dec(v_x_559_);
v___x_569_ = lean_array_push(v_ks_562_, v_x_560_);
v___x_570_ = lean_array_push(v_vs_563_, v_x_561_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v___x_570_);
lean_ctor_set(v___x_565_, 0, v___x_569_);
v___x_572_ = v___x_565_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
else
{
lean_object* v_k_x27_574_; uint8_t v___x_575_; 
v_k_x27_574_ = lean_array_fget_borrowed(v_ks_562_, v_x_559_);
v___x_575_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_560_, v_k_x27_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_577_; 
if (v_isShared_566_ == 0)
{
v___x_577_ = v___x_565_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_ks_562_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_vs_563_);
v___x_577_ = v_reuseFailAlloc_581_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_x_559_, v___x_578_);
lean_dec(v_x_559_);
v_x_558_ = v___x_577_;
v_x_559_ = v___x_579_;
goto _start;
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_582_ = lean_array_fset(v_ks_562_, v_x_559_, v_x_560_);
v___x_583_ = lean_array_fset(v_vs_563_, v_x_559_, v_x_561_);
lean_dec(v_x_559_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v___x_583_);
lean_ctor_set(v___x_565_, 0, v___x_582_);
v___x_585_ = v___x_565_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_588_, lean_object* v_k_589_, lean_object* v_v_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_588_, v___x_591_, v_k_589_, v_v_590_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(lean_object* v_x_594_, size_t v_x_595_, size_t v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_object* v_es_599_; size_t v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; lean_object* v_j_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_es_599_ = lean_ctor_get(v_x_594_, 0);
v___x_600_ = ((size_t)5ULL);
v___x_601_ = ((size_t)1ULL);
v___x_602_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_603_ = lean_usize_land(v_x_595_, v___x_602_);
v_j_604_ = lean_usize_to_nat(v___x_603_);
v___x_605_ = lean_array_get_size(v_es_599_);
v___x_606_ = lean_nat_dec_lt(v_j_604_, v___x_605_);
if (v___x_606_ == 0)
{
lean_dec(v_j_604_);
lean_dec(v_x_598_);
lean_dec_ref(v_x_597_);
return v_x_594_;
}
else
{
lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_643_; 
lean_inc_ref(v_es_599_);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_594_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v_x_594_, 0);
lean_dec(v_unused_644_);
v___x_608_ = v_x_594_;
v_isShared_609_ = v_isSharedCheck_643_;
goto v_resetjp_607_;
}
else
{
lean_dec(v_x_594_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_643_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_v_610_; lean_object* v___x_611_; lean_object* v_xs_x27_612_; lean_object* v___y_614_; 
v_v_610_ = lean_array_fget(v_es_599_, v_j_604_);
v___x_611_ = lean_box(0);
v_xs_x27_612_ = lean_array_fset(v_es_599_, v_j_604_, v___x_611_);
switch(lean_obj_tag(v_v_610_))
{
case 0:
{
lean_object* v_key_619_; lean_object* v_val_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_630_; 
v_key_619_ = lean_ctor_get(v_v_610_, 0);
v_val_620_ = lean_ctor_get(v_v_610_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_v_610_);
if (v_isSharedCheck_630_ == 0)
{
v___x_622_ = v_v_610_;
v_isShared_623_ = v_isSharedCheck_630_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_val_620_);
lean_inc(v_key_619_);
lean_dec(v_v_610_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_630_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
uint8_t v___x_624_; 
v___x_624_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_597_, v_key_619_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_del_object(v___x_622_);
v___x_625_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_619_, v_val_620_, v_x_597_, v_x_598_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___y_614_ = v___x_626_;
goto v___jp_613_;
}
else
{
lean_object* v___x_628_; 
lean_dec(v_val_620_);
lean_dec(v_key_619_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v_x_598_);
lean_ctor_set(v___x_622_, 0, v_x_597_);
v___x_628_ = v___x_622_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_x_597_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_x_598_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v___y_614_ = v___x_628_;
goto v___jp_613_;
}
}
}
}
case 1:
{
lean_object* v_node_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_641_; 
v_node_631_ = lean_ctor_get(v_v_610_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v_v_610_);
if (v_isSharedCheck_641_ == 0)
{
v___x_633_ = v_v_610_;
v_isShared_634_ = v_isSharedCheck_641_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_node_631_);
lean_dec(v_v_610_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_641_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
size_t v___x_635_; size_t v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_635_ = lean_usize_shift_right(v_x_595_, v___x_600_);
v___x_636_ = lean_usize_add(v_x_596_, v___x_601_);
v___x_637_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_node_631_, v___x_635_, v___x_636_, v_x_597_, v_x_598_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_637_);
v___x_639_ = v___x_633_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
v___y_614_ = v___x_639_;
goto v___jp_613_;
}
}
}
default: 
{
lean_object* v___x_642_; 
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v_x_597_);
lean_ctor_set(v___x_642_, 1, v_x_598_);
v___y_614_ = v___x_642_;
goto v___jp_613_;
}
}
v___jp_613_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_array_fset(v_xs_x27_612_, v_j_604_, v___y_614_);
lean_dec(v_j_604_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_615_);
v___x_617_ = v___x_608_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
else
{
lean_object* v_ks_645_; lean_object* v_vs_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_666_; 
v_ks_645_ = lean_ctor_get(v_x_594_, 0);
v_vs_646_ = lean_ctor_get(v_x_594_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_594_);
if (v_isSharedCheck_666_ == 0)
{
v___x_648_ = v_x_594_;
v_isShared_649_ = v_isSharedCheck_666_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_vs_646_);
lean_inc(v_ks_645_);
lean_dec(v_x_594_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_666_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_ks_645_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_vs_646_);
v___x_651_ = v_reuseFailAlloc_665_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v_newNode_652_; uint8_t v___y_654_; size_t v___x_660_; uint8_t v___x_661_; 
v_newNode_652_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(v___x_651_, v_x_597_, v_x_598_);
v___x_660_ = ((size_t)7ULL);
v___x_661_ = lean_usize_dec_le(v___x_660_, v_x_596_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_652_);
v___x_663_ = lean_unsigned_to_nat(4u);
v___x_664_ = lean_nat_dec_lt(v___x_662_, v___x_663_);
lean_dec(v___x_662_);
v___y_654_ = v___x_664_;
goto v___jp_653_;
}
else
{
v___y_654_ = v___x_661_;
goto v___jp_653_;
}
v___jp_653_:
{
if (v___y_654_ == 0)
{
lean_object* v_ks_655_; lean_object* v_vs_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_ks_655_ = lean_ctor_get(v_newNode_652_, 0);
lean_inc_ref(v_ks_655_);
v_vs_656_ = lean_ctor_get(v_newNode_652_, 1);
lean_inc_ref(v_vs_656_);
lean_dec_ref(v_newNode_652_);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0);
v___x_659_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_x_596_, v_ks_655_, v_vs_656_, v___x_657_, v___x_658_);
lean_dec_ref(v_vs_656_);
lean_dec_ref(v_ks_655_);
return v___x_659_;
}
else
{
return v_newNode_652_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(size_t v_depth_667_, lean_object* v_keys_668_, lean_object* v_vals_669_, lean_object* v_i_670_, lean_object* v_entries_671_){
_start:
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = lean_array_get_size(v_keys_668_);
v___x_673_ = lean_nat_dec_lt(v_i_670_, v___x_672_);
if (v___x_673_ == 0)
{
lean_dec(v_i_670_);
return v_entries_671_;
}
else
{
lean_object* v_k_674_; lean_object* v_v_675_; uint64_t v___x_676_; size_t v_h_677_; size_t v___x_678_; lean_object* v___x_679_; size_t v___x_680_; size_t v___x_681_; size_t v___x_682_; size_t v_h_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_k_674_ = lean_array_fget_borrowed(v_keys_668_, v_i_670_);
v_v_675_ = lean_array_fget_borrowed(v_vals_669_, v_i_670_);
v___x_676_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_674_);
v_h_677_ = lean_uint64_to_usize(v___x_676_);
v___x_678_ = ((size_t)5ULL);
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = ((size_t)1ULL);
v___x_681_ = lean_usize_sub(v_depth_667_, v___x_680_);
v___x_682_ = lean_usize_mul(v___x_678_, v___x_681_);
v_h_683_ = lean_usize_shift_right(v_h_677_, v___x_682_);
v___x_684_ = lean_nat_add(v_i_670_, v___x_679_);
lean_dec(v_i_670_);
lean_inc(v_v_675_);
lean_inc(v_k_674_);
v___x_685_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_entries_671_, v_h_683_, v_depth_667_, v_k_674_, v_v_675_);
v_i_670_ = v___x_684_;
v_entries_671_ = v___x_685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_687_, lean_object* v_keys_688_, lean_object* v_vals_689_, lean_object* v_i_690_, lean_object* v_entries_691_){
_start:
{
size_t v_depth_boxed_692_; lean_object* v_res_693_; 
v_depth_boxed_692_ = lean_unbox_usize(v_depth_687_);
lean_dec(v_depth_687_);
v_res_693_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_692_, v_keys_688_, v_vals_689_, v_i_690_, v_entries_691_);
lean_dec_ref(v_vals_689_);
lean_dec_ref(v_keys_688_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___boxed(lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
size_t v_x_8210__boxed_699_; size_t v_x_8211__boxed_700_; lean_object* v_res_701_; 
v_x_8210__boxed_699_ = lean_unbox_usize(v_x_695_);
lean_dec(v_x_695_);
v_x_8211__boxed_700_ = lean_unbox_usize(v_x_696_);
lean_dec(v_x_696_);
v_res_701_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_694_, v_x_8210__boxed_699_, v_x_8211__boxed_700_, v_x_697_, v_x_698_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_){
_start:
{
uint64_t v___x_705_; size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; 
v___x_705_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_703_);
v___x_706_ = lean_uint64_to_usize(v___x_705_);
v___x_707_ = ((size_t)1ULL);
v___x_708_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_702_, v___x_706_, v___x_707_, v_x_703_, v_x_704_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___lam__0(lean_object* v_e_709_, lean_object* v_a_710_, lean_object* v_s_711_){
_start:
{
lean_object* v_structs_712_; lean_object* v_typeIdOf_713_; lean_object* v_exprToStructId_714_; lean_object* v_exprToStructIdEntries_715_; lean_object* v_forbiddenNatModules_716_; lean_object* v_natStructs_717_; lean_object* v_natTypeIdOf_718_; lean_object* v_exprToNatStructId_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_727_; 
v_structs_712_ = lean_ctor_get(v_s_711_, 0);
v_typeIdOf_713_ = lean_ctor_get(v_s_711_, 1);
v_exprToStructId_714_ = lean_ctor_get(v_s_711_, 2);
v_exprToStructIdEntries_715_ = lean_ctor_get(v_s_711_, 3);
v_forbiddenNatModules_716_ = lean_ctor_get(v_s_711_, 4);
v_natStructs_717_ = lean_ctor_get(v_s_711_, 5);
v_natTypeIdOf_718_ = lean_ctor_get(v_s_711_, 6);
v_exprToNatStructId_719_ = lean_ctor_get(v_s_711_, 7);
v_isSharedCheck_727_ = !lean_is_exclusive(v_s_711_);
if (v_isSharedCheck_727_ == 0)
{
v___x_721_ = v_s_711_;
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_exprToNatStructId_719_);
lean_inc(v_natTypeIdOf_718_);
lean_inc(v_natStructs_717_);
lean_inc(v_forbiddenNatModules_716_);
lean_inc(v_exprToStructIdEntries_715_);
lean_inc(v_exprToStructId_714_);
lean_inc(v_typeIdOf_713_);
lean_inc(v_structs_712_);
lean_dec(v_s_711_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_exprToNatStructId_719_, v_e_709_, v_a_710_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 7, v___x_723_);
v___x_725_ = v___x_721_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_structs_712_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_typeIdOf_713_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_exprToStructId_714_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v_exprToStructIdEntries_715_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v_forbiddenNatModules_716_);
lean_ctor_set(v_reuseFailAlloc_726_, 5, v_natStructs_717_);
lean_ctor_set(v_reuseFailAlloc_726_, 6, v_natTypeIdOf_718_);
lean_ctor_set(v_reuseFailAlloc_726_, 7, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__1(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__0));
v___x_730_ = l_Lean_stringToMessageData(v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(lean_object* v_e_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_731_, v_a_733_, v_a_741_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref(v___x_747_);
if (lean_obj_tag(v_a_748_) == 1)
{
lean_object* v_val_749_; uint8_t v___x_750_; 
v_val_749_ = lean_ctor_get(v_a_748_, 0);
lean_inc(v_val_749_);
lean_dec_ref(v_a_748_);
v___x_750_ = lean_nat_dec_eq(v_val_749_, v_a_732_);
lean_dec(v_a_732_);
lean_dec(v_val_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_735_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; uint8_t v_verbose_753_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref(v___x_751_);
v_verbose_753_ = lean_ctor_get_uint8(v_a_752_, sizeof(void*)*11 + 15);
lean_dec(v_a_752_);
if (v_verbose_753_ == 0)
{
lean_dec_ref(v_e_731_);
goto v___jp_744_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_754_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__1);
v___x_755_ = l_Lean_indentExpr(v_e_731_);
v___x_756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = l_Lean_Meta_Grind_reportIssue(v___x_756_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_dec_ref(v___x_757_);
goto v___jp_744_;
}
else
{
return v___x_757_;
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v_e_731_);
v_a_758_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_751_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_751_);
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
else
{
lean_dec_ref(v_e_731_);
goto v___jp_744_;
}
}
else
{
lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec(v_a_748_);
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___lam__0), 3, 2);
lean_closure_set(v___f_766_, 0, v_e_731_);
lean_closure_set(v___f_766_, 1, v_a_732_);
v___x_767_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_768_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_767_, v___f_766_, v_a_733_);
return v___x_768_;
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec(v_a_732_);
lean_dec_ref(v_e_731_);
v_a_769_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_747_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_747_);
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
v___jp_744_:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_box(0);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___boxed(lean_object* v_e_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(v_e_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec(v_a_779_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0(lean_object* v_00_u03b2_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_x_792_, v_x_793_, v_x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(lean_object* v_00_u03b2_796_, lean_object* v_x_797_, size_t v_x_798_, size_t v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_797_, v_x_798_, v_x_799_, v_x_800_, v_x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_803_, lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
size_t v_x_8517__boxed_809_; size_t v_x_8518__boxed_810_; lean_object* v_res_811_; 
v_x_8517__boxed_809_ = lean_unbox_usize(v_x_805_);
lean_dec(v_x_805_);
v_x_8518__boxed_810_ = lean_unbox_usize(v_x_806_);
lean_dec(v_x_806_);
v_res_811_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(v_00_u03b2_803_, v_x_804_, v_x_8517__boxed_809_, v_x_8518__boxed_810_, v_x_807_, v_x_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_812_, lean_object* v_n_813_, lean_object* v_k_814_, lean_object* v_v_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(v_n_813_, v_k_814_, v_v_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_817_, size_t v_depth_818_, lean_object* v_keys_819_, lean_object* v_vals_820_, lean_object* v_heq_821_, lean_object* v_i_822_, lean_object* v_entries_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_818_, v_keys_819_, v_vals_820_, v_i_822_, v_entries_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_825_, lean_object* v_depth_826_, lean_object* v_keys_827_, lean_object* v_vals_828_, lean_object* v_heq_829_, lean_object* v_i_830_, lean_object* v_entries_831_){
_start:
{
size_t v_depth_boxed_832_; lean_object* v_res_833_; 
v_depth_boxed_832_ = lean_unbox_usize(v_depth_826_);
lean_dec(v_depth_826_);
v_res_833_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(v_00_u03b2_825_, v_depth_boxed_832_, v_keys_827_, v_vals_828_, v_heq_829_, v_i_830_, v_entries_831_);
lean_dec_ref(v_vals_828_);
lean_dec_ref(v_keys_827_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_835_, v_x_836_, v_x_837_, v_x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(lean_object* v_a_840_, lean_object* v_e_841_, lean_object* v___x_842_, lean_object* v_s_843_){
_start:
{
lean_object* v_structs_844_; lean_object* v_typeIdOf_845_; lean_object* v_exprToStructId_846_; lean_object* v_exprToStructIdEntries_847_; lean_object* v_forbiddenNatModules_848_; lean_object* v_natStructs_849_; lean_object* v_natTypeIdOf_850_; lean_object* v_exprToNatStructId_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v_structs_844_ = lean_ctor_get(v_s_843_, 0);
v_typeIdOf_845_ = lean_ctor_get(v_s_843_, 1);
v_exprToStructId_846_ = lean_ctor_get(v_s_843_, 2);
v_exprToStructIdEntries_847_ = lean_ctor_get(v_s_843_, 3);
v_forbiddenNatModules_848_ = lean_ctor_get(v_s_843_, 4);
v_natStructs_849_ = lean_ctor_get(v_s_843_, 5);
v_natTypeIdOf_850_ = lean_ctor_get(v_s_843_, 6);
v_exprToNatStructId_851_ = lean_ctor_get(v_s_843_, 7);
v___x_852_ = lean_array_get_size(v_natStructs_849_);
v___x_853_ = lean_nat_dec_lt(v_a_840_, v___x_852_);
if (v___x_853_ == 0)
{
lean_dec_ref(v___x_842_);
lean_dec_ref(v_e_841_);
return v_s_843_;
}
else
{
lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_890_; 
lean_inc_ref(v_exprToNatStructId_851_);
lean_inc_ref(v_natTypeIdOf_850_);
lean_inc_ref(v_natStructs_849_);
lean_inc_ref(v_forbiddenNatModules_848_);
lean_inc_ref(v_exprToStructIdEntries_847_);
lean_inc_ref(v_exprToStructId_846_);
lean_inc_ref(v_typeIdOf_845_);
lean_inc_ref(v_structs_844_);
v_isSharedCheck_890_ = !lean_is_exclusive(v_s_843_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; lean_object* v_unused_892_; lean_object* v_unused_893_; lean_object* v_unused_894_; lean_object* v_unused_895_; lean_object* v_unused_896_; lean_object* v_unused_897_; lean_object* v_unused_898_; 
v_unused_891_ = lean_ctor_get(v_s_843_, 7);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_s_843_, 6);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_s_843_, 5);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_s_843_, 4);
lean_dec(v_unused_894_);
v_unused_895_ = lean_ctor_get(v_s_843_, 3);
lean_dec(v_unused_895_);
v_unused_896_ = lean_ctor_get(v_s_843_, 2);
lean_dec(v_unused_896_);
v_unused_897_ = lean_ctor_get(v_s_843_, 1);
lean_dec(v_unused_897_);
v_unused_898_ = lean_ctor_get(v_s_843_, 0);
lean_dec(v_unused_898_);
v___x_855_ = v_s_843_;
v_isShared_856_ = v_isSharedCheck_890_;
goto v_resetjp_854_;
}
else
{
lean_dec(v_s_843_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_890_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_v_857_; lean_object* v_id_858_; lean_object* v_structId_859_; lean_object* v_type_860_; lean_object* v_u_861_; lean_object* v_natModuleInst_862_; lean_object* v_leInst_x3f_863_; lean_object* v_ltInst_x3f_864_; lean_object* v_lawfulOrderLTInst_x3f_865_; lean_object* v_isPreorderInst_x3f_866_; lean_object* v_orderedAddInst_x3f_867_; lean_object* v_isLinearInst_x3f_868_; lean_object* v_addRightCancelInst_x3f_869_; lean_object* v_rfl__q_870_; lean_object* v_zero_871_; lean_object* v_toQFn_872_; lean_object* v_addFn_873_; lean_object* v_smulFn_874_; lean_object* v_termMap_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_889_; 
v_v_857_ = lean_array_fget(v_natStructs_849_, v_a_840_);
v_id_858_ = lean_ctor_get(v_v_857_, 0);
v_structId_859_ = lean_ctor_get(v_v_857_, 1);
v_type_860_ = lean_ctor_get(v_v_857_, 2);
v_u_861_ = lean_ctor_get(v_v_857_, 3);
v_natModuleInst_862_ = lean_ctor_get(v_v_857_, 4);
v_leInst_x3f_863_ = lean_ctor_get(v_v_857_, 5);
v_ltInst_x3f_864_ = lean_ctor_get(v_v_857_, 6);
v_lawfulOrderLTInst_x3f_865_ = lean_ctor_get(v_v_857_, 7);
v_isPreorderInst_x3f_866_ = lean_ctor_get(v_v_857_, 8);
v_orderedAddInst_x3f_867_ = lean_ctor_get(v_v_857_, 9);
v_isLinearInst_x3f_868_ = lean_ctor_get(v_v_857_, 10);
v_addRightCancelInst_x3f_869_ = lean_ctor_get(v_v_857_, 11);
v_rfl__q_870_ = lean_ctor_get(v_v_857_, 12);
v_zero_871_ = lean_ctor_get(v_v_857_, 13);
v_toQFn_872_ = lean_ctor_get(v_v_857_, 14);
v_addFn_873_ = lean_ctor_get(v_v_857_, 15);
v_smulFn_874_ = lean_ctor_get(v_v_857_, 16);
v_termMap_875_ = lean_ctor_get(v_v_857_, 17);
v_isSharedCheck_889_ = !lean_is_exclusive(v_v_857_);
if (v_isSharedCheck_889_ == 0)
{
v___x_877_ = v_v_857_;
v_isShared_878_ = v_isSharedCheck_889_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_termMap_875_);
lean_inc(v_smulFn_874_);
lean_inc(v_addFn_873_);
lean_inc(v_toQFn_872_);
lean_inc(v_zero_871_);
lean_inc(v_rfl__q_870_);
lean_inc(v_addRightCancelInst_x3f_869_);
lean_inc(v_isLinearInst_x3f_868_);
lean_inc(v_orderedAddInst_x3f_867_);
lean_inc(v_isPreorderInst_x3f_866_);
lean_inc(v_lawfulOrderLTInst_x3f_865_);
lean_inc(v_ltInst_x3f_864_);
lean_inc(v_leInst_x3f_863_);
lean_inc(v_natModuleInst_862_);
lean_inc(v_u_861_);
lean_inc(v_type_860_);
lean_inc(v_structId_859_);
lean_inc(v_id_858_);
lean_dec(v_v_857_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_889_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v_xs_x27_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_879_ = lean_box(0);
v_xs_x27_880_ = lean_array_fset(v_natStructs_849_, v_a_840_, v___x_879_);
v___x_881_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_875_, v_e_841_, v___x_842_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 17, v___x_881_);
v___x_883_ = v___x_877_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_id_858_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_structId_859_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_type_860_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_u_861_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_natModuleInst_862_);
lean_ctor_set(v_reuseFailAlloc_888_, 5, v_leInst_x3f_863_);
lean_ctor_set(v_reuseFailAlloc_888_, 6, v_ltInst_x3f_864_);
lean_ctor_set(v_reuseFailAlloc_888_, 7, v_lawfulOrderLTInst_x3f_865_);
lean_ctor_set(v_reuseFailAlloc_888_, 8, v_isPreorderInst_x3f_866_);
lean_ctor_set(v_reuseFailAlloc_888_, 9, v_orderedAddInst_x3f_867_);
lean_ctor_set(v_reuseFailAlloc_888_, 10, v_isLinearInst_x3f_868_);
lean_ctor_set(v_reuseFailAlloc_888_, 11, v_addRightCancelInst_x3f_869_);
lean_ctor_set(v_reuseFailAlloc_888_, 12, v_rfl__q_870_);
lean_ctor_set(v_reuseFailAlloc_888_, 13, v_zero_871_);
lean_ctor_set(v_reuseFailAlloc_888_, 14, v_toQFn_872_);
lean_ctor_set(v_reuseFailAlloc_888_, 15, v_addFn_873_);
lean_ctor_set(v_reuseFailAlloc_888_, 16, v_smulFn_874_);
lean_ctor_set(v_reuseFailAlloc_888_, 17, v___x_881_);
v___x_883_ = v_reuseFailAlloc_888_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_array_fset(v_xs_x27_880_, v_a_840_, v___x_883_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 5, v___x_884_);
v___x_886_ = v___x_855_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_structs_844_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_typeIdOf_845_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_exprToStructId_846_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v_exprToStructIdEntries_847_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v_forbiddenNatModules_848_);
lean_ctor_set(v_reuseFailAlloc_887_, 5, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_887_, 6, v_natTypeIdOf_850_);
lean_ctor_set(v_reuseFailAlloc_887_, 7, v_exprToNatStructId_851_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed(lean_object* v_a_899_, lean_object* v_e_900_, lean_object* v___x_901_, lean_object* v_s_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(v_a_899_, v_e_900_, v___x_901_, v_s_902_);
lean_dec(v_a_899_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(lean_object* v_e_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_990_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_990_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_990_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_990_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_termMap_922_; lean_object* v___x_923_; 
v_termMap_922_ = lean_ctor_get(v_a_918_, 17);
lean_inc_ref(v_termMap_922_);
lean_dec(v_a_918_);
v___x_923_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_922_, v_e_904_);
if (lean_obj_tag(v___x_923_) == 1)
{
lean_object* v_val_924_; lean_object* v___x_926_; 
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_e_904_);
v_val_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_val_924_);
lean_dec_ref(v___x_923_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v_val_924_);
v___x_926_ = v___x_920_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_val_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
else
{
lean_object* v___x_928_; 
lean_dec(v___x_923_);
lean_del_object(v___x_920_);
v___x_928_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v_rfl__q_930_; lean_object* v_toQFn_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v___x_928_);
v_rfl__q_930_ = lean_ctor_get(v_a_929_, 12);
lean_inc_ref(v_rfl__q_930_);
v_toQFn_931_ = lean_ctor_get(v_a_929_, 14);
lean_inc_ref(v_toQFn_931_);
lean_dec(v_a_929_);
lean_inc_ref(v_e_904_);
v___x_932_ = l_Lean_Expr_app___override(v_toQFn_931_, v_e_904_);
v___x_933_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_932_, v_a_911_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___f_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref(v___x_933_);
lean_inc(v_a_934_);
v___x_935_ = l_Lean_Expr_app___override(v_rfl__q_930_, v_a_934_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v_a_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
lean_inc_ref(v___x_936_);
lean_inc_ref(v_e_904_);
lean_inc(v_a_905_);
v___f_937_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed), 4, 3);
lean_closure_set(v___f_937_, 0, v_a_905_);
lean_closure_set(v___f_937_, 1, v_e_904_);
lean_closure_set(v___f_937_, 2, v___x_936_);
v___x_938_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_939_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_938_, v___f_937_, v_a_906_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v___x_940_; 
lean_dec_ref(v___x_939_);
lean_inc_ref(v_e_904_);
v___x_940_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(v_e_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v___x_941_; 
lean_dec_ref(v___x_940_);
v___x_941_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_938_, v_e_904_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v___x_941_, 0);
lean_dec(v_unused_949_);
v___x_943_ = v___x_941_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_dec(v___x_941_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_936_);
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_936_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v___x_936_);
v_a_950_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_941_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_941_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec_ref(v___x_936_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_e_904_);
v_a_958_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_940_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_940_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec_ref(v___x_936_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_e_904_);
v_a_966_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_939_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_939_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v_rfl__q_930_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_e_904_);
v_a_974_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_933_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_933_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_e_904_);
v_a_982_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_928_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_928_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_e_904_);
v_a_991_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_917_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_917_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___boxed(lean_object* v_e_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(lean_object* v_natStruct_1013_, lean_object* v_inst_1014_){
_start:
{
lean_object* v_addFn_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_addFn_1015_ = lean_ctor_get(v_natStruct_1013_, 15);
v___x_1016_ = l_Lean_Expr_appArg_x21(v_addFn_1015_);
v___x_1017_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1016_, v_inst_1014_);
lean_dec_ref(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(lean_object* v_natStruct_1018_, lean_object* v_inst_1019_){
_start:
{
uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_res_1020_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_natStruct_1018_, v_inst_1019_);
lean_dec_ref(v_inst_1019_);
lean_dec_ref(v_natStruct_1018_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(lean_object* v_natStruct_1022_, lean_object* v_inst_1023_){
_start:
{
lean_object* v_zero_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_zero_1024_ = lean_ctor_get(v_natStruct_1022_, 13);
v___x_1025_ = l_Lean_Expr_appArg_x21(v_zero_1024_);
v___x_1026_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1025_, v_inst_1023_);
lean_dec_ref(v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(lean_object* v_natStruct_1027_, lean_object* v_inst_1028_){
_start:
{
uint8_t v_res_1029_; lean_object* v_r_1030_; 
v_res_1029_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_natStruct_1027_, v_inst_1028_);
lean_dec_ref(v_inst_1028_);
lean_dec_ref(v_natStruct_1027_);
v_r_1030_ = lean_box(v_res_1029_);
return v_r_1030_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(lean_object* v_natStruct_1031_, lean_object* v_inst_1032_){
_start:
{
lean_object* v_smulFn_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_smulFn_1033_ = lean_ctor_get(v_natStruct_1031_, 16);
v___x_1034_ = l_Lean_Expr_appArg_x21(v_smulFn_1033_);
v___x_1035_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1034_, v_inst_1032_);
lean_dec_ref(v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst___boxed(lean_object* v_natStruct_1036_, lean_object* v_inst_1037_){
_start:
{
uint8_t v_res_1038_; lean_object* v_r_1039_; 
v_res_1038_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_natStruct_1036_, v_inst_1037_);
lean_dec_ref(v_inst_1037_);
lean_dec_ref(v_natStruct_1036_);
v_r_1039_ = lean_box(v_res_1038_);
return v_r_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(lean_object* v_e_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1100_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref(v___x_1098_);
v___x_1100_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1102_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref(v___x_1100_);
lean_inc_ref(v_e_1085_);
v___x_1102_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1085_, v_a_1094_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1253_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1253_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1253_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = l_Lean_Expr_cleanupAnnotations(v_a_1103_);
v___x_1108_ = l_Lean_Expr_isApp(v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; 
lean_dec_ref(v___x_1107_);
lean_del_object(v___x_1105_);
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
v___x_1109_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1109_;
}
else
{
lean_object* v_arg_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v_arg_1110_ = lean_ctor_get(v___x_1107_, 1);
lean_inc_ref(v_arg_1110_);
v___x_1111_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1107_);
v___x_1112_ = l_Lean_Expr_isApp(v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
lean_dec_ref(v___x_1111_);
lean_dec_ref(v_arg_1110_);
lean_del_object(v___x_1105_);
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
v___x_1113_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1113_;
}
else
{
lean_object* v_arg_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_arg_1114_ = lean_ctor_get(v___x_1111_, 1);
lean_inc_ref(v_arg_1114_);
v___x_1115_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1111_);
v___x_1116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2));
v___x_1117_ = l_Lean_Expr_isConstOf(v___x_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
uint8_t v___x_1118_; 
lean_del_object(v___x_1105_);
v___x_1118_ = l_Lean_Expr_isApp(v___x_1115_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1110_);
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
v___x_1119_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1119_;
}
else
{
lean_object* v_arg_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_arg_1120_ = lean_ctor_get(v___x_1115_, 1);
lean_inc_ref(v_arg_1120_);
v___x_1121_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1115_);
v___x_1122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5));
v___x_1123_ = l_Lean_Expr_isConstOf(v___x_1121_, v___x_1122_);
if (v___x_1123_ == 0)
{
uint8_t v___x_1124_; 
v___x_1124_ = l_Lean_Expr_isApp(v___x_1121_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec_ref(v___x_1121_);
lean_dec_ref(v_arg_1120_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1110_);
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
v___x_1125_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1121_);
v___x_1127_ = l_Lean_Expr_isApp(v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v___x_1126_);
lean_dec_ref(v_arg_1120_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1110_);
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
v___x_1128_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1126_);
v___x_1130_ = l_Lean_Expr_isApp(v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_dec_ref(v___x_1129_);
lean_dec_ref(v_arg_1120_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1110_);
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
v___x_1131_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1132_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1129_);
v___x_1133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8));
v___x_1134_ = l_Lean_Expr_isConstOf(v___x_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11));
v___x_1136_ = l_Lean_Expr_isConstOf(v___x_1132_, v___x_1135_);
lean_dec_ref(v___x_1132_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; 
lean_dec_ref(v_arg_1120_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1110_);
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
v___x_1137_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1137_;
}
else
{
uint8_t v___x_1138_; 
v___x_1138_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1101_, v_arg_1120_);
lean_dec_ref(v_arg_1120_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1110_);
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
v___x_1139_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; 
lean_dec_ref(v_e_1085_);
lean_inc(v_a_1096_);
lean_inc_ref(v_a_1095_);
lean_inc(v_a_1094_);
lean_inc_ref(v_a_1093_);
lean_inc(v_a_1092_);
lean_inc_ref(v_a_1091_);
lean_inc(v_a_1090_);
lean_inc_ref(v_a_1089_);
lean_inc(v_a_1088_);
lean_inc(v_a_1087_);
lean_inc(v_a_1086_);
lean_inc_ref(v_arg_1114_);
v___x_1140_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1114_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v_fst_1142_; lean_object* v_snd_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1177_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref(v___x_1140_);
v_fst_1142_ = lean_ctor_get(v_a_1141_, 0);
v_snd_1143_ = lean_ctor_get(v_a_1141_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_a_1141_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1145_ = v_a_1141_;
v_isShared_1146_ = v_isSharedCheck_1177_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_snd_1143_);
lean_inc(v_fst_1142_);
lean_dec(v_a_1141_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1177_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; 
lean_inc_ref(v_arg_1110_);
v___x_1147_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1110_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1176_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1176_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1176_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_fst_1152_; lean_object* v_snd_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1175_; 
v_fst_1152_ = lean_ctor_get(v_a_1148_, 0);
v_snd_1153_ = lean_ctor_get(v_a_1148_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_a_1148_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1155_ = v_a_1148_;
v_isShared_1156_ = v_isSharedCheck_1175_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_snd_1153_);
lean_inc(v_fst_1152_);
lean_dec(v_a_1148_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1175_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v_addFn_1157_; lean_object* v_type_1158_; lean_object* v_u_1159_; lean_object* v_natModuleInst_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v_addFn_1157_ = lean_ctor_get(v_a_1099_, 22);
lean_inc_ref(v_addFn_1157_);
lean_dec(v_a_1099_);
v_type_1158_ = lean_ctor_get(v_a_1101_, 2);
lean_inc_ref(v_type_1158_);
v_u_1159_ = lean_ctor_get(v_a_1101_, 3);
lean_inc(v_u_1159_);
v_natModuleInst_1160_ = lean_ctor_get(v_a_1101_, 4);
lean_inc_ref(v_natModuleInst_1160_);
lean_dec(v_a_1101_);
lean_inc(v_fst_1152_);
lean_inc(v_fst_1142_);
v___x_1161_ = l_Lean_mkAppB(v_addFn_1157_, v_fst_1142_, v_fst_1152_);
v___x_1162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17));
v___x_1163_ = lean_box(0);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 1);
lean_ctor_set(v___x_1145_, 1, v___x_1163_);
lean_ctor_set(v___x_1145_, 0, v_u_1159_);
v___x_1165_ = v___x_1145_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_u_1159_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1166_ = l_Lean_mkConst(v___x_1162_, v___x_1165_);
v___x_1167_ = l_Lean_mkApp8(v___x_1166_, v_type_1158_, v_natModuleInst_1160_, v_arg_1114_, v_arg_1110_, v_fst_1142_, v_fst_1152_, v_snd_1143_, v_snd_1153_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 1, v___x_1167_);
lean_ctor_set(v___x_1155_, 0, v___x_1161_);
v___x_1169_ = v___x_1155_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1171_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1169_);
v___x_1171_ = v___x_1150_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1145_);
lean_dec(v_snd_1143_);
lean_dec(v_fst_1142_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1110_);
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
return v___x_1147_;
}
}
}
else
{
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1110_);
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec(v_a_1086_);
return v___x_1140_;
}
}
}
}
else
{
uint8_t v___x_1178_; 
lean_dec_ref(v___x_1132_);
v___x_1178_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_1101_, v_arg_1120_);
lean_dec_ref(v_arg_1120_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1110_);
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
v___x_1179_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1179_;
}
else
{
lean_object* v___x_1180_; 
lean_dec_ref(v_e_1085_);
lean_inc_ref(v_arg_1110_);
v___x_1180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1110_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1207_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1207_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1207_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v_fst_1185_; lean_object* v_snd_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1206_; 
v_fst_1185_ = lean_ctor_get(v_a_1181_, 0);
v_snd_1186_ = lean_ctor_get(v_a_1181_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_a_1181_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1188_ = v_a_1181_;
v_isShared_1189_ = v_isSharedCheck_1206_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_snd_1186_);
lean_inc(v_fst_1185_);
lean_dec(v_a_1181_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1206_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_nsmulFn_1190_; lean_object* v_type_1191_; lean_object* v_u_1192_; lean_object* v_natModuleInst_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v_nsmulFn_1190_ = lean_ctor_get(v_a_1099_, 24);
lean_inc_ref(v_nsmulFn_1190_);
lean_dec(v_a_1099_);
v_type_1191_ = lean_ctor_get(v_a_1101_, 2);
lean_inc_ref(v_type_1191_);
v_u_1192_ = lean_ctor_get(v_a_1101_, 3);
lean_inc(v_u_1192_);
v_natModuleInst_1193_ = lean_ctor_get(v_a_1101_, 4);
lean_inc_ref(v_natModuleInst_1193_);
lean_dec(v_a_1101_);
lean_inc(v_fst_1185_);
lean_inc_ref(v_arg_1114_);
v___x_1194_ = l_Lean_mkAppB(v_nsmulFn_1190_, v_arg_1114_, v_fst_1185_);
v___x_1195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19));
v___x_1196_ = lean_box(0);
v___x_1197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_u_1192_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = l_Lean_mkConst(v___x_1195_, v___x_1197_);
v___x_1199_ = l_Lean_mkApp6(v___x_1198_, v_type_1191_, v_natModuleInst_1193_, v_arg_1114_, v_arg_1110_, v_fst_1185_, v_snd_1186_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v___x_1199_);
lean_ctor_set(v___x_1188_, 0, v___x_1194_);
v___x_1201_ = v___x_1188_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1203_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1201_);
v___x_1203_ = v___x_1183_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1110_);
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
return v___x_1180_;
}
}
}
}
}
}
}
else
{
lean_object* v_type_1208_; lean_object* v_u_1209_; lean_object* v_natModuleInst_1210_; lean_object* v_zero_1211_; lean_object* v___x_1212_; 
lean_dec_ref(v___x_1121_);
lean_dec_ref(v_arg_1120_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1110_);
v_type_1208_ = lean_ctor_get(v_a_1101_, 2);
lean_inc_ref(v_type_1208_);
v_u_1209_ = lean_ctor_get(v_a_1101_, 3);
lean_inc(v_u_1209_);
v_natModuleInst_1210_ = lean_ctor_get(v_a_1101_, 4);
lean_inc_ref(v_natModuleInst_1210_);
v_zero_1211_ = lean_ctor_get(v_a_1101_, 13);
lean_inc_ref(v_zero_1211_);
lean_dec(v_a_1101_);
lean_inc(v_a_1096_);
lean_inc_ref(v_a_1095_);
lean_inc(v_a_1094_);
lean_inc_ref(v_a_1093_);
lean_inc_ref(v_e_1085_);
v___x_1212_ = l_Lean_Meta_isDefEqD(v_e_1085_, v_zero_1211_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1229_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1229_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1229_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_unbox(v_a_1213_);
lean_dec(v_a_1213_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
lean_del_object(v___x_1215_);
lean_dec_ref(v_natModuleInst_1210_);
lean_dec(v_u_1209_);
lean_dec_ref(v_type_1208_);
lean_dec(v_a_1099_);
v___x_1218_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1218_;
}
else
{
lean_object* v_zero_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_e_1085_);
v_zero_1219_ = lean_ctor_get(v_a_1099_, 17);
lean_inc_ref(v_zero_1219_);
lean_dec(v_a_1099_);
v___x_1220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21));
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_u_1209_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = l_Lean_mkConst(v___x_1220_, v___x_1222_);
v___x_1224_ = l_Lean_mkAppB(v___x_1223_, v_type_1208_, v_natModuleInst_1210_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v_zero_1219_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1225_);
v___x_1227_ = v___x_1215_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec_ref(v_natModuleInst_1210_);
lean_dec(v_u_1209_);
lean_dec_ref(v_type_1208_);
lean_dec(v_a_1099_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_e_1085_);
v_a_1230_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1212_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1212_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
}
else
{
uint8_t v___x_1238_; 
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_arg_1114_);
v___x_1238_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_1101_, v_arg_1110_);
lean_dec_ref(v_arg_1110_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_del_object(v___x_1105_);
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
v___x_1239_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1239_;
}
else
{
lean_object* v_zero_1240_; lean_object* v_type_1241_; lean_object* v_u_1242_; lean_object* v_natModuleInst_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_e_1085_);
v_zero_1240_ = lean_ctor_get(v_a_1099_, 17);
lean_inc_ref(v_zero_1240_);
lean_dec(v_a_1099_);
v_type_1241_ = lean_ctor_get(v_a_1101_, 2);
lean_inc_ref(v_type_1241_);
v_u_1242_ = lean_ctor_get(v_a_1101_, 3);
lean_inc(v_u_1242_);
v_natModuleInst_1243_ = lean_ctor_get(v_a_1101_, 4);
lean_inc_ref(v_natModuleInst_1243_);
lean_dec(v_a_1101_);
v___x_1244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21));
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_u_1242_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = l_Lean_mkConst(v___x_1244_, v___x_1246_);
v___x_1248_ = l_Lean_mkAppB(v___x_1247_, v_type_1241_, v_natModuleInst_1243_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v_zero_1240_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1249_);
v___x_1251_ = v___x_1105_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v_a_1101_);
lean_dec(v_a_1099_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_e_1085_);
v_a_1254_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1102_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1102_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_a_1099_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_e_1085_);
v_a_1262_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1100_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1100_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_e_1085_);
v_a_1270_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1098_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1098_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___boxed(lean_object* v_e_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(lean_object* v___y_1292_, lean_object* v_e_1293_, lean_object* v_____x_1294_, lean_object* v_s_1295_){
_start:
{
lean_object* v_structs_1296_; lean_object* v_typeIdOf_1297_; lean_object* v_exprToStructId_1298_; lean_object* v_exprToStructIdEntries_1299_; lean_object* v_forbiddenNatModules_1300_; lean_object* v_natStructs_1301_; lean_object* v_natTypeIdOf_1302_; lean_object* v_exprToNatStructId_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_structs_1296_ = lean_ctor_get(v_s_1295_, 0);
v_typeIdOf_1297_ = lean_ctor_get(v_s_1295_, 1);
v_exprToStructId_1298_ = lean_ctor_get(v_s_1295_, 2);
v_exprToStructIdEntries_1299_ = lean_ctor_get(v_s_1295_, 3);
v_forbiddenNatModules_1300_ = lean_ctor_get(v_s_1295_, 4);
v_natStructs_1301_ = lean_ctor_get(v_s_1295_, 5);
v_natTypeIdOf_1302_ = lean_ctor_get(v_s_1295_, 6);
v_exprToNatStructId_1303_ = lean_ctor_get(v_s_1295_, 7);
v___x_1304_ = lean_array_get_size(v_natStructs_1301_);
v___x_1305_ = lean_nat_dec_lt(v___y_1292_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_dec_ref(v_____x_1294_);
lean_dec_ref(v_e_1293_);
return v_s_1295_;
}
else
{
lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1342_; 
lean_inc_ref(v_exprToNatStructId_1303_);
lean_inc_ref(v_natTypeIdOf_1302_);
lean_inc_ref(v_natStructs_1301_);
lean_inc_ref(v_forbiddenNatModules_1300_);
lean_inc_ref(v_exprToStructIdEntries_1299_);
lean_inc_ref(v_exprToStructId_1298_);
lean_inc_ref(v_typeIdOf_1297_);
lean_inc_ref(v_structs_1296_);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_s_1295_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; lean_object* v_unused_1344_; lean_object* v_unused_1345_; lean_object* v_unused_1346_; lean_object* v_unused_1347_; lean_object* v_unused_1348_; lean_object* v_unused_1349_; lean_object* v_unused_1350_; 
v_unused_1343_ = lean_ctor_get(v_s_1295_, 7);
lean_dec(v_unused_1343_);
v_unused_1344_ = lean_ctor_get(v_s_1295_, 6);
lean_dec(v_unused_1344_);
v_unused_1345_ = lean_ctor_get(v_s_1295_, 5);
lean_dec(v_unused_1345_);
v_unused_1346_ = lean_ctor_get(v_s_1295_, 4);
lean_dec(v_unused_1346_);
v_unused_1347_ = lean_ctor_get(v_s_1295_, 3);
lean_dec(v_unused_1347_);
v_unused_1348_ = lean_ctor_get(v_s_1295_, 2);
lean_dec(v_unused_1348_);
v_unused_1349_ = lean_ctor_get(v_s_1295_, 1);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v_s_1295_, 0);
lean_dec(v_unused_1350_);
v___x_1307_ = v_s_1295_;
v_isShared_1308_ = v_isSharedCheck_1342_;
goto v_resetjp_1306_;
}
else
{
lean_dec(v_s_1295_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1342_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_v_1309_; lean_object* v_id_1310_; lean_object* v_structId_1311_; lean_object* v_type_1312_; lean_object* v_u_1313_; lean_object* v_natModuleInst_1314_; lean_object* v_leInst_x3f_1315_; lean_object* v_ltInst_x3f_1316_; lean_object* v_lawfulOrderLTInst_x3f_1317_; lean_object* v_isPreorderInst_x3f_1318_; lean_object* v_orderedAddInst_x3f_1319_; lean_object* v_isLinearInst_x3f_1320_; lean_object* v_addRightCancelInst_x3f_1321_; lean_object* v_rfl__q_1322_; lean_object* v_zero_1323_; lean_object* v_toQFn_1324_; lean_object* v_addFn_1325_; lean_object* v_smulFn_1326_; lean_object* v_termMap_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1341_; 
v_v_1309_ = lean_array_fget(v_natStructs_1301_, v___y_1292_);
v_id_1310_ = lean_ctor_get(v_v_1309_, 0);
v_structId_1311_ = lean_ctor_get(v_v_1309_, 1);
v_type_1312_ = lean_ctor_get(v_v_1309_, 2);
v_u_1313_ = lean_ctor_get(v_v_1309_, 3);
v_natModuleInst_1314_ = lean_ctor_get(v_v_1309_, 4);
v_leInst_x3f_1315_ = lean_ctor_get(v_v_1309_, 5);
v_ltInst_x3f_1316_ = lean_ctor_get(v_v_1309_, 6);
v_lawfulOrderLTInst_x3f_1317_ = lean_ctor_get(v_v_1309_, 7);
v_isPreorderInst_x3f_1318_ = lean_ctor_get(v_v_1309_, 8);
v_orderedAddInst_x3f_1319_ = lean_ctor_get(v_v_1309_, 9);
v_isLinearInst_x3f_1320_ = lean_ctor_get(v_v_1309_, 10);
v_addRightCancelInst_x3f_1321_ = lean_ctor_get(v_v_1309_, 11);
v_rfl__q_1322_ = lean_ctor_get(v_v_1309_, 12);
v_zero_1323_ = lean_ctor_get(v_v_1309_, 13);
v_toQFn_1324_ = lean_ctor_get(v_v_1309_, 14);
v_addFn_1325_ = lean_ctor_get(v_v_1309_, 15);
v_smulFn_1326_ = lean_ctor_get(v_v_1309_, 16);
v_termMap_1327_ = lean_ctor_get(v_v_1309_, 17);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_v_1309_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1329_ = v_v_1309_;
v_isShared_1330_ = v_isSharedCheck_1341_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_termMap_1327_);
lean_inc(v_smulFn_1326_);
lean_inc(v_addFn_1325_);
lean_inc(v_toQFn_1324_);
lean_inc(v_zero_1323_);
lean_inc(v_rfl__q_1322_);
lean_inc(v_addRightCancelInst_x3f_1321_);
lean_inc(v_isLinearInst_x3f_1320_);
lean_inc(v_orderedAddInst_x3f_1319_);
lean_inc(v_isPreorderInst_x3f_1318_);
lean_inc(v_lawfulOrderLTInst_x3f_1317_);
lean_inc(v_ltInst_x3f_1316_);
lean_inc(v_leInst_x3f_1315_);
lean_inc(v_natModuleInst_1314_);
lean_inc(v_u_1313_);
lean_inc(v_type_1312_);
lean_inc(v_structId_1311_);
lean_inc(v_id_1310_);
lean_dec(v_v_1309_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1341_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v_xs_x27_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1331_ = lean_box(0);
v_xs_x27_1332_ = lean_array_fset(v_natStructs_1301_, v___y_1292_, v___x_1331_);
v___x_1333_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_1327_, v_e_1293_, v_____x_1294_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 17, v___x_1333_);
v___x_1335_ = v___x_1329_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_id_1310_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_structId_1311_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_type_1312_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_u_1313_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_natModuleInst_1314_);
lean_ctor_set(v_reuseFailAlloc_1340_, 5, v_leInst_x3f_1315_);
lean_ctor_set(v_reuseFailAlloc_1340_, 6, v_ltInst_x3f_1316_);
lean_ctor_set(v_reuseFailAlloc_1340_, 7, v_lawfulOrderLTInst_x3f_1317_);
lean_ctor_set(v_reuseFailAlloc_1340_, 8, v_isPreorderInst_x3f_1318_);
lean_ctor_set(v_reuseFailAlloc_1340_, 9, v_orderedAddInst_x3f_1319_);
lean_ctor_set(v_reuseFailAlloc_1340_, 10, v_isLinearInst_x3f_1320_);
lean_ctor_set(v_reuseFailAlloc_1340_, 11, v_addRightCancelInst_x3f_1321_);
lean_ctor_set(v_reuseFailAlloc_1340_, 12, v_rfl__q_1322_);
lean_ctor_set(v_reuseFailAlloc_1340_, 13, v_zero_1323_);
lean_ctor_set(v_reuseFailAlloc_1340_, 14, v_toQFn_1324_);
lean_ctor_set(v_reuseFailAlloc_1340_, 15, v_addFn_1325_);
lean_ctor_set(v_reuseFailAlloc_1340_, 16, v_smulFn_1326_);
lean_ctor_set(v_reuseFailAlloc_1340_, 17, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1336_ = lean_array_fset(v_xs_x27_1332_, v___y_1292_, v___x_1335_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 5, v___x_1336_);
v___x_1338_ = v___x_1307_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_structs_1296_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_typeIdOf_1297_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_exprToStructId_1298_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_exprToStructIdEntries_1299_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v_forbiddenNatModules_1300_);
lean_ctor_set(v_reuseFailAlloc_1339_, 5, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1339_, 6, v_natTypeIdOf_1302_);
lean_ctor_set(v_reuseFailAlloc_1339_, 7, v_exprToNatStructId_1303_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed(lean_object* v___y_1351_, lean_object* v_e_1352_, lean_object* v_____x_1353_, lean_object* v_s_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(v___y_1351_, v_e_1352_, v_____x_1353_, v_s_1354_);
lean_dec(v___y_1351_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule(lean_object* v_e_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_____x_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1459_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1459_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1459_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_termMap_1415_; lean_object* v___x_1416_; 
v_termMap_1415_ = lean_ctor_get(v_a_1411_, 17);
lean_inc_ref(v_termMap_1415_);
lean_dec(v_a_1411_);
v___x_1416_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_1415_, v_e_1356_);
if (lean_obj_tag(v___x_1416_) == 1)
{
lean_object* v_val_1417_; lean_object* v___x_1419_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_e_1356_);
v_val_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_val_1417_);
lean_dec_ref(v___x_1416_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v_val_1417_);
v___x_1419_ = v___x_1413_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_val_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
else
{
lean_object* v___x_1421_; 
lean_dec(v___x_1416_);
lean_del_object(v___x_1413_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_a_1363_);
lean_inc_ref(v_a_1362_);
lean_inc(v_a_1361_);
lean_inc_ref(v_a_1360_);
lean_inc(v_a_1359_);
lean_inc(v_a_1358_);
lean_inc(v_a_1357_);
lean_inc_ref(v_e_1356_);
v___x_1421_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v_fst_1423_; lean_object* v_snd_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1458_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref(v___x_1421_);
v_fst_1423_ = lean_ctor_get(v_a_1422_, 0);
v_snd_1424_ = lean_ctor_get(v_a_1422_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_a_1422_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1426_ = v_a_1422_;
v_isShared_1427_ = v_isSharedCheck_1458_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_snd_1424_);
lean_inc(v_fst_1423_);
lean_dec(v_a_1422_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1458_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_a_1363_);
lean_inc_ref(v_a_1362_);
lean_inc(v_a_1361_);
lean_inc_ref(v_a_1360_);
lean_inc(v_a_1359_);
lean_inc(v_a_1358_);
v___x_1428_ = lean_grind_preprocess(v_fst_1423_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v_proof_x3f_1430_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref(v___x_1428_);
v_proof_x3f_1430_ = lean_ctor_get(v_a_1429_, 1);
if (lean_obj_tag(v_proof_x3f_1430_) == 1)
{
lean_object* v_expr_1431_; lean_object* v_val_1432_; lean_object* v___x_1433_; 
lean_inc_ref(v_proof_x3f_1430_);
v_expr_1431_ = lean_ctor_get(v_a_1429_, 0);
lean_inc_ref(v_expr_1431_);
lean_dec(v_a_1429_);
v_val_1432_ = lean_ctor_get(v_proof_x3f_1430_, 0);
lean_inc(v_val_1432_);
lean_dec_ref(v_proof_x3f_1430_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1433_ = l_Lean_Meta_mkEqTrans(v_snd_1424_, v_val_1432_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref(v___x_1433_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v_a_1434_);
lean_ctor_set(v___x_1426_, 0, v_expr_1431_);
v___x_1436_ = v___x_1426_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_expr_1431_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_a_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
v_____x_1370_ = v___x_1436_;
v___y_1371_ = v_a_1357_;
v___y_1372_ = v_a_1358_;
v___y_1373_ = v_a_1359_;
v___y_1374_ = v_a_1360_;
v___y_1375_ = v_a_1361_;
v___y_1376_ = v_a_1362_;
v___y_1377_ = v_a_1363_;
v___y_1378_ = v_a_1364_;
v___y_1379_ = v_a_1365_;
v___y_1380_ = v_a_1366_;
v___y_1381_ = v_a_1367_;
goto v___jp_1369_;
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v_expr_1431_);
lean_del_object(v___x_1426_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_e_1356_);
v_a_1438_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1433_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1433_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_expr_1446_; lean_object* v___x_1448_; 
v_expr_1446_ = lean_ctor_get(v_a_1429_, 0);
lean_inc_ref(v_expr_1446_);
lean_dec(v_a_1429_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v_expr_1446_);
v___x_1448_ = v___x_1426_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_expr_1446_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_snd_1424_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
v_____x_1370_ = v___x_1448_;
v___y_1371_ = v_a_1357_;
v___y_1372_ = v_a_1358_;
v___y_1373_ = v_a_1359_;
v___y_1374_ = v_a_1360_;
v___y_1375_ = v_a_1361_;
v___y_1376_ = v_a_1362_;
v___y_1377_ = v_a_1363_;
v___y_1378_ = v_a_1364_;
v___y_1379_ = v_a_1365_;
v___y_1380_ = v_a_1366_;
v___y_1381_ = v_a_1367_;
goto v___jp_1369_;
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_del_object(v___x_1426_);
lean_dec(v_snd_1424_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_e_1356_);
v_a_1450_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1428_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1428_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
else
{
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_e_1356_);
return v___x_1421_;
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_e_1356_);
v_a_1460_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1410_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1410_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
v___jp_1369_:
{
lean_object* v___x_1382_; 
lean_inc(v___y_1371_);
lean_inc_ref(v_e_1356_);
v___x_1382_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(v_e_1356_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___f_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec_ref(v___x_1382_);
lean_inc_ref(v_____x_1370_);
v___f_1383_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1383_, 0, v___y_1371_);
lean_closure_set(v___f_1383_, 1, v_e_1356_);
lean_closure_set(v___f_1383_, 2, v_____x_1370_);
v___x_1384_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1385_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1384_, v___f_1383_, v___y_1372_);
lean_dec(v___y_1372_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v___x_1385_, 0);
lean_dec(v_unused_1393_);
v___x_1387_ = v___x_1385_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v___x_1385_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v_____x_1370_);
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_____x_1370_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec_ref(v_____x_1370_);
v_a_1394_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1385_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1385_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v_____x_1370_);
lean_dec_ref(v_e_1356_);
v_a_1402_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1382_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1382_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___boxed(lean_object* v_e_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_e_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
return v_res_1481_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = lean_box(0);
v___x_1483_ = lean_unsigned_to_nat(16u);
v___x_1484_ = lean_mk_array(v___x_1483_, v___x_1482_);
return v___x_1484_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0);
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v___x_1485_);
return v___x_1487_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2));
v___x_1491_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___x_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(lean_object* v_x_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_1507_ = lean_st_mk_ref(v___x_1506_);
lean_inc(v___x_1507_);
v___x_1508_ = lean_apply_13(v_x_1493_, v___x_1507_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, lean_box(0));
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1517_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1513_ = lean_st_ref_get(v___x_1507_);
lean_dec(v___x_1507_);
lean_dec(v___x_1513_);
if (v_isShared_1512_ == 0)
{
v___x_1515_ = v___x_1511_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1509_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
else
{
lean_dec(v___x_1507_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___boxed(lean_object* v_x_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(v_x_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(lean_object* v_00_u03b1_1532_, lean_object* v_x_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_1547_ = lean_st_mk_ref(v___x_1546_);
lean_inc(v___x_1547_);
v___x_1548_ = lean_apply_13(v_x_1533_, v___x_1547_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, lean_box(0));
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1557_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1557_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1557_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1553_ = lean_st_ref_get(v___x_1547_);
lean_dec(v___x_1547_);
lean_dec(v___x_1553_);
if (v_isShared_1552_ == 0)
{
v___x_1555_ = v___x_1551_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1549_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
else
{
lean_dec(v___x_1547_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___boxed(lean_object* v_00_u03b1_1558_, lean_object* v_x_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(v_00_u03b1_1558_, v_x_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(lean_object* v_a_1573_, lean_object* v_b_1574_, lean_object* v_x_1575_){
_start:
{
if (lean_obj_tag(v_x_1575_) == 0)
{
lean_dec(v_b_1574_);
lean_dec_ref(v_a_1573_);
return v_x_1575_;
}
else
{
lean_object* v_key_1576_; lean_object* v_value_1577_; lean_object* v_tail_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1590_; 
v_key_1576_ = lean_ctor_get(v_x_1575_, 0);
v_value_1577_ = lean_ctor_get(v_x_1575_, 1);
v_tail_1578_ = lean_ctor_get(v_x_1575_, 2);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1580_ = v_x_1575_;
v_isShared_1581_ = v_isSharedCheck_1590_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_tail_1578_);
lean_inc(v_value_1577_);
lean_inc(v_key_1576_);
lean_dec(v_x_1575_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1590_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
uint8_t v___x_1582_; 
v___x_1582_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_1576_, v_a_1573_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1573_, v_b_1574_, v_tail_1578_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 2, v___x_1583_);
v___x_1585_ = v___x_1580_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_key_1576_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_value_1577_);
lean_ctor_set(v_reuseFailAlloc_1586_, 2, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
else
{
lean_object* v___x_1588_; 
lean_dec(v_value_1577_);
lean_dec(v_key_1576_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 1, v_b_1574_);
lean_ctor_set(v___x_1580_, 0, v_a_1573_);
v___x_1588_ = v___x_1580_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1573_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_b_1574_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_tail_1578_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1591_, lean_object* v_x_1592_){
_start:
{
if (lean_obj_tag(v_x_1592_) == 0)
{
return v_x_1591_;
}
else
{
lean_object* v_key_1593_; lean_object* v_value_1594_; lean_object* v_tail_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1618_; 
v_key_1593_ = lean_ctor_get(v_x_1592_, 0);
v_value_1594_ = lean_ctor_get(v_x_1592_, 1);
v_tail_1595_ = lean_ctor_get(v_x_1592_, 2);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1597_ = v_x_1592_;
v_isShared_1598_ = v_isSharedCheck_1618_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_tail_1595_);
lean_inc(v_value_1594_);
lean_inc(v_key_1593_);
lean_dec(v_x_1592_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1618_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; uint64_t v___x_1600_; uint64_t v___x_1601_; uint64_t v___x_1602_; uint64_t v_fold_1603_; uint64_t v___x_1604_; uint64_t v___x_1605_; uint64_t v___x_1606_; size_t v___x_1607_; size_t v___x_1608_; size_t v___x_1609_; size_t v___x_1610_; size_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1599_ = lean_array_get_size(v_x_1591_);
v___x_1600_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_1593_);
v___x_1601_ = 32ULL;
v___x_1602_ = lean_uint64_shift_right(v___x_1600_, v___x_1601_);
v_fold_1603_ = lean_uint64_xor(v___x_1600_, v___x_1602_);
v___x_1604_ = 16ULL;
v___x_1605_ = lean_uint64_shift_right(v_fold_1603_, v___x_1604_);
v___x_1606_ = lean_uint64_xor(v_fold_1603_, v___x_1605_);
v___x_1607_ = lean_uint64_to_usize(v___x_1606_);
v___x_1608_ = lean_usize_of_nat(v___x_1599_);
v___x_1609_ = ((size_t)1ULL);
v___x_1610_ = lean_usize_sub(v___x_1608_, v___x_1609_);
v___x_1611_ = lean_usize_land(v___x_1607_, v___x_1610_);
v___x_1612_ = lean_array_uget_borrowed(v_x_1591_, v___x_1611_);
lean_inc(v___x_1612_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 2, v___x_1612_);
v___x_1614_ = v___x_1597_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_key_1593_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_value_1594_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_array_uset(v_x_1591_, v___x_1611_, v___x_1614_);
v_x_1591_ = v___x_1615_;
v_x_1592_ = v_tail_1595_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1619_, lean_object* v_source_1620_, lean_object* v_target_1621_){
_start:
{
lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = lean_array_get_size(v_source_1620_);
v___x_1623_ = lean_nat_dec_lt(v_i_1619_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_dec_ref(v_source_1620_);
lean_dec(v_i_1619_);
return v_target_1621_;
}
else
{
lean_object* v_es_1624_; lean_object* v___x_1625_; lean_object* v_source_1626_; lean_object* v_target_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_es_1624_ = lean_array_fget(v_source_1620_, v_i_1619_);
v___x_1625_ = lean_box(0);
v_source_1626_ = lean_array_fset(v_source_1620_, v_i_1619_, v___x_1625_);
v_target_1627_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1621_, v_es_1624_);
v___x_1628_ = lean_unsigned_to_nat(1u);
v___x_1629_ = lean_nat_add(v_i_1619_, v___x_1628_);
lean_dec(v_i_1619_);
v_i_1619_ = v___x_1629_;
v_source_1620_ = v_source_1626_;
v_target_1621_ = v_target_1627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(lean_object* v_data_1631_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v_nbuckets_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1632_ = lean_array_get_size(v_data_1631_);
v___x_1633_ = lean_unsigned_to_nat(2u);
v_nbuckets_1634_ = lean_nat_mul(v___x_1632_, v___x_1633_);
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = lean_box(0);
v___x_1637_ = lean_mk_array(v_nbuckets_1634_, v___x_1636_);
v___x_1638_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v___x_1635_, v_data_1631_, v___x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(lean_object* v_a_1639_, lean_object* v_x_1640_){
_start:
{
if (lean_obj_tag(v_x_1640_) == 0)
{
uint8_t v___x_1641_; 
v___x_1641_ = 0;
return v___x_1641_;
}
else
{
lean_object* v_key_1642_; lean_object* v_tail_1643_; uint8_t v___x_1644_; 
v_key_1642_ = lean_ctor_get(v_x_1640_, 0);
v_tail_1643_ = lean_ctor_get(v_x_1640_, 2);
v___x_1644_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_1642_, v_a_1639_);
if (v___x_1644_ == 0)
{
v_x_1640_ = v_tail_1643_;
goto _start;
}
else
{
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg___boxed(lean_object* v_a_1646_, lean_object* v_x_1647_){
_start:
{
uint8_t v_res_1648_; lean_object* v_r_1649_; 
v_res_1648_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1646_, v_x_1647_);
lean_dec(v_x_1647_);
lean_dec_ref(v_a_1646_);
v_r_1649_ = lean_box(v_res_1648_);
return v_r_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(lean_object* v_m_1650_, lean_object* v_a_1651_, lean_object* v_b_1652_){
_start:
{
lean_object* v_size_1653_; lean_object* v_buckets_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1697_; 
v_size_1653_ = lean_ctor_get(v_m_1650_, 0);
v_buckets_1654_ = lean_ctor_get(v_m_1650_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_m_1650_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1656_ = v_m_1650_;
v_isShared_1657_ = v_isSharedCheck_1697_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_buckets_1654_);
lean_inc(v_size_1653_);
lean_dec(v_m_1650_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1697_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; uint64_t v___x_1659_; uint64_t v___x_1660_; uint64_t v___x_1661_; uint64_t v_fold_1662_; uint64_t v___x_1663_; uint64_t v___x_1664_; uint64_t v___x_1665_; size_t v___x_1666_; size_t v___x_1667_; size_t v___x_1668_; size_t v___x_1669_; size_t v___x_1670_; lean_object* v_bkt_1671_; uint8_t v___x_1672_; 
v___x_1658_ = lean_array_get_size(v_buckets_1654_);
v___x_1659_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_1651_);
v___x_1660_ = 32ULL;
v___x_1661_ = lean_uint64_shift_right(v___x_1659_, v___x_1660_);
v_fold_1662_ = lean_uint64_xor(v___x_1659_, v___x_1661_);
v___x_1663_ = 16ULL;
v___x_1664_ = lean_uint64_shift_right(v_fold_1662_, v___x_1663_);
v___x_1665_ = lean_uint64_xor(v_fold_1662_, v___x_1664_);
v___x_1666_ = lean_uint64_to_usize(v___x_1665_);
v___x_1667_ = lean_usize_of_nat(v___x_1658_);
v___x_1668_ = ((size_t)1ULL);
v___x_1669_ = lean_usize_sub(v___x_1667_, v___x_1668_);
v___x_1670_ = lean_usize_land(v___x_1666_, v___x_1669_);
v_bkt_1671_ = lean_array_uget_borrowed(v_buckets_1654_, v___x_1670_);
v___x_1672_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1651_, v_bkt_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v_size_x27_1674_; lean_object* v___x_1675_; lean_object* v_buckets_x27_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1673_ = lean_unsigned_to_nat(1u);
v_size_x27_1674_ = lean_nat_add(v_size_1653_, v___x_1673_);
lean_dec(v_size_1653_);
lean_inc(v_bkt_1671_);
v___x_1675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1675_, 0, v_a_1651_);
lean_ctor_set(v___x_1675_, 1, v_b_1652_);
lean_ctor_set(v___x_1675_, 2, v_bkt_1671_);
v_buckets_x27_1676_ = lean_array_uset(v_buckets_1654_, v___x_1670_, v___x_1675_);
v___x_1677_ = lean_unsigned_to_nat(4u);
v___x_1678_ = lean_nat_mul(v_size_x27_1674_, v___x_1677_);
v___x_1679_ = lean_unsigned_to_nat(3u);
v___x_1680_ = lean_nat_div(v___x_1678_, v___x_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_array_get_size(v_buckets_x27_1676_);
v___x_1682_ = lean_nat_dec_le(v___x_1680_, v___x_1681_);
lean_dec(v___x_1680_);
if (v___x_1682_ == 0)
{
lean_object* v_val_1683_; lean_object* v___x_1685_; 
v_val_1683_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_buckets_x27_1676_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 1, v_val_1683_);
lean_ctor_set(v___x_1656_, 0, v_size_x27_1674_);
v___x_1685_ = v___x_1656_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_size_x27_1674_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_val_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
else
{
lean_object* v___x_1688_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 1, v_buckets_x27_1676_);
lean_ctor_set(v___x_1656_, 0, v_size_x27_1674_);
v___x_1688_ = v___x_1656_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_size_x27_1674_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_buckets_x27_1676_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
else
{
lean_object* v___x_1690_; lean_object* v_buckets_x27_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1695_; 
lean_inc(v_bkt_1671_);
v___x_1690_ = lean_box(0);
v_buckets_x27_1691_ = lean_array_uset(v_buckets_1654_, v___x_1670_, v___x_1690_);
v___x_1692_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1651_, v_b_1652_, v_bkt_1671_);
v___x_1693_ = lean_array_uset(v_buckets_x27_1691_, v___x_1670_, v___x_1692_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 1, v___x_1693_);
v___x_1695_ = v___x_1656_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_size_1653_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(lean_object* v_a_1698_, lean_object* v_x_1699_){
_start:
{
if (lean_obj_tag(v_x_1699_) == 0)
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_box(0);
return v___x_1700_;
}
else
{
lean_object* v_key_1701_; lean_object* v_value_1702_; lean_object* v_tail_1703_; uint8_t v___x_1704_; 
v_key_1701_ = lean_ctor_get(v_x_1699_, 0);
v_value_1702_ = lean_ctor_get(v_x_1699_, 1);
v_tail_1703_ = lean_ctor_get(v_x_1699_, 2);
v___x_1704_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_1701_, v_a_1698_);
if (v___x_1704_ == 0)
{
v_x_1699_ = v_tail_1703_;
goto _start;
}
else
{
lean_object* v___x_1706_; 
lean_inc(v_value_1702_);
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_value_1702_);
return v___x_1706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_1707_, lean_object* v_x_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1707_, v_x_1708_);
lean_dec(v_x_1708_);
lean_dec_ref(v_a_1707_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(lean_object* v_m_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_buckets_1712_; lean_object* v___x_1713_; uint64_t v___x_1714_; uint64_t v___x_1715_; uint64_t v___x_1716_; uint64_t v_fold_1717_; uint64_t v___x_1718_; uint64_t v___x_1719_; uint64_t v___x_1720_; size_t v___x_1721_; size_t v___x_1722_; size_t v___x_1723_; size_t v___x_1724_; size_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_buckets_1712_ = lean_ctor_get(v_m_1710_, 1);
v___x_1713_ = lean_array_get_size(v_buckets_1712_);
v___x_1714_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_1711_);
v___x_1715_ = 32ULL;
v___x_1716_ = lean_uint64_shift_right(v___x_1714_, v___x_1715_);
v_fold_1717_ = lean_uint64_xor(v___x_1714_, v___x_1716_);
v___x_1718_ = 16ULL;
v___x_1719_ = lean_uint64_shift_right(v_fold_1717_, v___x_1718_);
v___x_1720_ = lean_uint64_xor(v_fold_1717_, v___x_1719_);
v___x_1721_ = lean_uint64_to_usize(v___x_1720_);
v___x_1722_ = lean_usize_of_nat(v___x_1713_);
v___x_1723_ = ((size_t)1ULL);
v___x_1724_ = lean_usize_sub(v___x_1722_, v___x_1723_);
v___x_1725_ = lean_usize_land(v___x_1721_, v___x_1724_);
v___x_1726_ = lean_array_uget_borrowed(v_buckets_1712_, v___x_1725_);
v___x_1727_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1711_, v___x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg___boxed(lean_object* v_m_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_1728_, v_a_1729_);
lean_dec_ref(v_a_1729_);
lean_dec_ref(v_m_1728_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(lean_object* v_e_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; lean_object* v_varMap_1735_; lean_object* v___x_1736_; 
v___x_1734_ = lean_st_ref_get(v_a_1732_);
v_varMap_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc_ref(v_varMap_1735_);
lean_dec(v___x_1734_);
v___x_1736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_varMap_1735_, v_e_1731_);
lean_dec_ref(v_varMap_1735_);
if (lean_obj_tag(v___x_1736_) == 1)
{
lean_object* v_val_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1745_; 
lean_dec_ref(v_e_1731_);
v_val_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1745_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_val_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1745_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_val_1737_);
v___x_1742_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
return v___x_1743_;
}
}
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v_vars_1748_; lean_object* v_varMap_1749_; lean_object* v_vars_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v___x_1736_);
v___x_1746_ = lean_st_ref_get(v_a_1732_);
v___x_1747_ = lean_st_ref_take(v_a_1732_);
v_vars_1748_ = lean_ctor_get(v___x_1746_, 1);
lean_inc_ref(v_vars_1748_);
lean_dec(v___x_1746_);
v_varMap_1749_ = lean_ctor_get(v___x_1747_, 0);
v_vars_1750_ = lean_ctor_get(v___x_1747_, 1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1752_ = v___x_1747_;
v_isShared_1753_ = v_isSharedCheck_1763_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_vars_1750_);
lean_inc(v_varMap_1749_);
lean_dec(v___x_1747_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1763_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1754_ = lean_array_get_size(v_vars_1748_);
lean_dec_ref(v_vars_1748_);
lean_inc_ref(v_e_1731_);
v___x_1755_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_varMap_1749_, v_e_1731_, v___x_1754_);
v___x_1756_ = lean_array_push(v_vars_1750_, v_e_1731_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 1, v___x_1756_);
lean_ctor_set(v___x_1752_, 0, v___x_1755_);
v___x_1758_ = v___x_1752_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = lean_st_ref_set(v_a_1732_, v___x_1758_);
v___x_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1754_);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg___boxed(lean_object* v_e_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1764_, v_a_1765_);
lean_dec(v_a_1765_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(lean_object* v_e_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1768_, v_a_1769_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___boxed(lean_object* v_e_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(v_e_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec(v_a_1784_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(lean_object* v_00_u03b2_1798_, lean_object* v_m_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_1799_, v_a_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___boxed(lean_object* v_00_u03b2_1802_, lean_object* v_m_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(v_00_u03b2_1802_, v_m_1803_, v_a_1804_);
lean_dec_ref(v_a_1804_);
lean_dec_ref(v_m_1803_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1(lean_object* v_00_u03b2_1806_, lean_object* v_m_1807_, lean_object* v_a_1808_, lean_object* v_b_1809_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_m_1807_, v_a_1808_, v_b_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(lean_object* v_00_u03b2_1811_, lean_object* v_a_1812_, lean_object* v_x_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1812_, v_x_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1815_, lean_object* v_a_1816_, lean_object* v_x_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(v_00_u03b2_1815_, v_a_1816_, v_x_1817_);
lean_dec(v_x_1817_);
lean_dec_ref(v_a_1816_);
return v_res_1818_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(lean_object* v_00_u03b2_1819_, lean_object* v_a_1820_, lean_object* v_x_1821_){
_start:
{
uint8_t v___x_1822_; 
v___x_1822_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1820_, v_x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1823_, lean_object* v_a_1824_, lean_object* v_x_1825_){
_start:
{
uint8_t v_res_1826_; lean_object* v_r_1827_; 
v_res_1826_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(v_00_u03b2_1823_, v_a_1824_, v_x_1825_);
lean_dec(v_x_1825_);
lean_dec_ref(v_a_1824_);
v_r_1827_ = lean_box(v_res_1826_);
return v_r_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3(lean_object* v_00_u03b2_1828_, lean_object* v_data_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_data_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4(lean_object* v_00_u03b2_1831_, lean_object* v_a_1832_, lean_object* v_b_1833_, lean_object* v_x_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1832_, v_b_1833_, v_x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1836_, lean_object* v_i_1837_, lean_object* v_source_1838_, lean_object* v_target_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v_i_1837_, v_source_1838_, v_target_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1841_, lean_object* v_x_1842_, lean_object* v_x_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1842_, v_x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(lean_object* v_e_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1861_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1859_);
lean_inc_ref(v_e_1845_);
v___x_1861_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1845_, v_a_1855_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1962_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1864_ = v___x_1861_;
v_isShared_1865_ = v_isSharedCheck_1962_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1861_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1962_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = l_Lean_Expr_cleanupAnnotations(v_a_1862_);
v___x_1867_ = l_Lean_Expr_isApp(v___x_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
lean_dec_ref(v___x_1866_);
lean_del_object(v___x_1864_);
lean_dec(v_a_1860_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
v___x_1868_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1845_, v_a_1846_);
return v___x_1868_;
}
else
{
lean_object* v_arg_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v_arg_1869_ = lean_ctor_get(v___x_1866_, 1);
lean_inc_ref(v_arg_1869_);
v___x_1870_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1866_);
v___x_1871_ = l_Lean_Expr_isApp(v___x_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
lean_dec_ref(v___x_1870_);
lean_dec_ref(v_arg_1869_);
lean_del_object(v___x_1864_);
lean_dec(v_a_1860_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
v___x_1872_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1845_, v_a_1846_);
return v___x_1872_;
}
else
{
lean_object* v_arg_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v_arg_1873_ = lean_ctor_get(v___x_1870_, 1);
lean_inc_ref(v_arg_1873_);
v___x_1874_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1870_);
v___x_1875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2));
v___x_1876_ = l_Lean_Expr_isConstOf(v___x_1874_, v___x_1875_);
if (v___x_1876_ == 0)
{
uint8_t v___x_1877_; 
lean_del_object(v___x_1864_);
v___x_1877_ = l_Lean_Expr_isApp(v___x_1874_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; 
lean_dec_ref(v___x_1874_);
lean_dec_ref(v_arg_1873_);
lean_dec_ref(v_arg_1869_);
lean_dec(v_a_1860_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
v___x_1878_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1845_, v_a_1846_);
return v___x_1878_;
}
else
{
lean_object* v_arg_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; 
v_arg_1879_ = lean_ctor_get(v___x_1874_, 1);
lean_inc_ref(v_arg_1879_);
v___x_1880_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1874_);
v___x_1881_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5));
v___x_1882_ = l_Lean_Expr_isConstOf(v___x_1880_, v___x_1881_);
if (v___x_1882_ == 0)
{
uint8_t v___x_1883_; 
v___x_1883_ = l_Lean_Expr_isApp(v___x_1880_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
lean_dec_ref(v___x_1880_);
lean_dec_ref(v_arg_1879_);
lean_dec_ref(v_arg_1873_);
lean_dec_ref(v_arg_1869_);
lean_dec(v_a_1860_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
v___x_1884_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1845_, v_a_1846_);
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1880_);
v___x_1886_ = l_Lean_Expr_isApp(v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; 
lean_dec_ref(v___x_1885_);
lean_dec_ref(v_arg_1879_);
lean_dec_ref(v_arg_1873_);
lean_dec_ref(v_arg_1869_);
lean_dec(v_a_1860_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
v___x_1887_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1845_, v_a_1846_);
return v___x_1887_;
}
else
{
lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1888_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1885_);
v___x_1889_ = l_Lean_Expr_isApp(v___x_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; 
lean_dec_ref(v___x_1888_);
lean_dec_ref(v_arg_1879_);
lean_dec_ref(v_arg_1873_);
lean_dec_ref(v_arg_1869_);
lean_dec(v_a_1860_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
v___x_1890_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1845_, v_a_1846_);
return v___x_1890_;
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1891_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1888_);
v___x_1892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8));
v___x_1893_ = l_Lean_Expr_isConstOf(v___x_1891_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11));
v___x_1895_ = l_Lean_Expr_isConstOf(v___x_1891_, v___x_1894_);
lean_dec_ref(v___x_1891_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; 
lean_dec_ref(v_arg_1879_);
lean_dec_ref(v_arg_1873_);
lean_dec_ref(v_arg_1869_);
lean_dec(v_a_1860_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
v___x_1896_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1845_, v_a_1846_);
return v___x_1896_;
}
else
{
uint8_t v___x_1897_; 
v___x_1897_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1860_, v_arg_1879_);
lean_dec_ref(v_arg_1879_);
lean_dec(v_a_1860_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; 
lean_dec_ref(v_arg_1873_);
lean_dec_ref(v_arg_1869_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
v___x_1898_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1845_, v_a_1846_);
return v___x_1898_;
}
else
{
lean_object* v___x_1899_; 
lean_dec_ref(v_e_1845_);
lean_inc(v_a_1857_);
lean_inc_ref(v_a_1856_);
lean_inc(v_a_1855_);
lean_inc_ref(v_a_1854_);
v___x_1899_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_1873_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1901_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1899_);
v___x_1901_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_1869_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1910_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1910_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1910_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1906_, 0, v_a_1900_);
lean_ctor_set(v___x_1906_, 1, v_a_1902_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1906_);
v___x_1908_ = v___x_1904_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
else
{
lean_dec(v_a_1900_);
return v___x_1901_;
}
}
else
{
lean_dec_ref(v_arg_1869_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
return v___x_1899_;
}
}
}
}
else
{
uint8_t v___x_1911_; 
lean_dec_ref(v___x_1891_);
v___x_1911_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_1860_, v_arg_1879_);
lean_dec_ref(v_arg_1879_);
lean_dec(v_a_1860_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; 
lean_dec_ref(v_arg_1873_);
lean_dec_ref(v_arg_1869_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
v___x_1912_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1845_, v_a_1846_);
return v___x_1912_;
}
else
{
lean_object* v___x_1913_; 
lean_inc(v_a_1857_);
lean_inc_ref(v_a_1856_);
lean_inc(v_a_1855_);
lean_inc_ref(v_a_1854_);
v___x_1913_ = l_Lean_Meta_getNatValue_x3f(v_arg_1873_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
lean_dec_ref(v_arg_1873_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref(v___x_1913_);
if (lean_obj_tag(v_a_1914_) == 1)
{
lean_object* v_val_1915_; lean_object* v___x_1916_; 
lean_dec_ref(v_e_1845_);
v_val_1915_ = lean_ctor_get(v_a_1914_, 0);
lean_inc(v_val_1915_);
lean_dec_ref(v_a_1914_);
v___x_1916_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_1869_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1925_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_val_1915_);
lean_ctor_set(v___x_1921_, 1, v_a_1917_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1921_);
v___x_1923_ = v___x_1919_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
else
{
lean_dec(v_val_1915_);
return v___x_1916_;
}
}
else
{
lean_object* v___x_1926_; 
lean_dec(v_a_1914_);
lean_dec_ref(v_arg_1869_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
v___x_1926_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1845_, v_a_1846_);
return v___x_1926_;
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec_ref(v_arg_1869_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec_ref(v_e_1845_);
v_a_1927_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1913_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1913_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_zero_1935_; lean_object* v___x_1936_; 
lean_dec_ref(v___x_1880_);
lean_dec_ref(v_arg_1879_);
lean_dec_ref(v_arg_1873_);
lean_dec_ref(v_arg_1869_);
v_zero_1935_ = lean_ctor_get(v_a_1860_, 13);
lean_inc_ref(v_zero_1935_);
lean_dec(v_a_1860_);
lean_inc_ref(v_e_1845_);
v___x_1936_ = l_Lean_Meta_isDefEqD(v_e_1845_, v_zero_1935_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1947_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1947_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1947_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_unbox(v_a_1937_);
lean_dec(v_a_1937_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; 
lean_del_object(v___x_1939_);
v___x_1942_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1845_, v_a_1846_);
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
lean_dec_ref(v_e_1845_);
v___x_1943_ = lean_box(0);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1943_);
v___x_1945_ = v___x_1939_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v_e_1845_);
v_a_1948_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1936_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1936_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
}
else
{
uint8_t v___x_1956_; 
lean_dec_ref(v___x_1874_);
lean_dec_ref(v_arg_1873_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
v___x_1956_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_1860_, v_arg_1869_);
lean_dec_ref(v_arg_1869_);
lean_dec(v_a_1860_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; 
lean_del_object(v___x_1864_);
v___x_1957_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1845_, v_a_1846_);
return v___x_1957_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
lean_dec_ref(v_e_1845_);
v___x_1958_ = lean_box(0);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1958_);
v___x_1960_ = v___x_1864_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v_a_1860_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec_ref(v_e_1845_);
v_a_1963_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1861_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1861_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec_ref(v_e_1845_);
v_a_1971_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1859_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1859_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify___boxed(lean_object* v_e_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_e_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec(v_a_1980_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(lean_object* v_a_2001_, lean_object* v_b_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_ctx_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v___x_2020_; 
lean_inc(v___y_2018_);
lean_inc_ref(v___y_2017_);
lean_inc(v___y_2016_);
lean_inc_ref(v___y_2015_);
lean_inc(v___y_2014_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2012_);
lean_inc_ref(v___y_2011_);
lean_inc(v___y_2010_);
lean_inc(v___y_2009_);
v___x_2020_ = l_Lean_Meta_Grind_mkDiseqProof(v_a_2001_, v_b_2002_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v_type_2022_; lean_object* v_u_2023_; lean_object* v_natModuleInst_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref(v___x_2020_);
v_type_2022_ = lean_ctor_get(v_a_2003_, 2);
lean_inc_ref(v_type_2022_);
v_u_2023_ = lean_ctor_get(v_a_2003_, 3);
lean_inc(v_u_2023_);
v_natModuleInst_2024_ = lean_ctor_get(v_a_2003_, 4);
lean_inc_ref(v_natModuleInst_2024_);
lean_dec_ref(v_a_2003_);
v___x_2025_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2));
v___x_2026_ = lean_box(0);
v___x_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_u_2023_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = l_Lean_mkConst(v___x_2025_, v___x_2027_);
v___x_2029_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_2004_);
v___x_2030_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_2005_);
v___x_2031_ = l_Lean_eagerReflBoolTrue;
v___x_2032_ = l_Lean_mkApp6(v___x_2028_, v_type_2022_, v_natModuleInst_2024_, v_ctx_2006_, v___x_2029_, v___x_2030_, v___x_2031_);
v___x_2033_ = l_Lean_Expr_app___override(v_a_2021_, v___x_2032_);
v___x_2034_ = l_Lean_Meta_Grind_closeGoal(v___x_2033_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec(v___y_2009_);
return v___x_2034_;
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v_ctx_2006_);
lean_dec(v_a_2005_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
v_a_2035_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2020_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2020_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___boxed(lean_object** _args){
lean_object* v_a_2043_ = _args[0];
lean_object* v_b_2044_ = _args[1];
lean_object* v_a_2045_ = _args[2];
lean_object* v_a_2046_ = _args[3];
lean_object* v_a_2047_ = _args[4];
lean_object* v_ctx_2048_ = _args[5];
lean_object* v___y_2049_ = _args[6];
lean_object* v___y_2050_ = _args[7];
lean_object* v___y_2051_ = _args[8];
lean_object* v___y_2052_ = _args[9];
lean_object* v___y_2053_ = _args[10];
lean_object* v___y_2054_ = _args[11];
lean_object* v___y_2055_ = _args[12];
lean_object* v___y_2056_ = _args[13];
lean_object* v___y_2057_ = _args[14];
lean_object* v___y_2058_ = _args[15];
lean_object* v___y_2059_ = _args[16];
lean_object* v___y_2060_ = _args[17];
lean_object* v___y_2061_ = _args[18];
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v_a_2043_, v_b_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_ctx_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2050_);
lean_dec(v___y_2049_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(lean_object* v___y_2063_){
_start:
{
lean_inc_ref(v___y_2063_);
return v___y_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed(lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(v___y_2064_);
lean_dec_ref(v___y_2064_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3(lean_object* v_vars_2066_, lean_object* v_x_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_array_fget_borrowed(v_vars_2066_, v_x_2067_);
lean_inc(v___x_2068_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3___boxed(lean_object* v_vars_2069_, lean_object* v_x_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3(v_vars_2069_, v_x_2070_);
lean_dec(v_x_2070_);
lean_dec_ref(v_vars_2069_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(lean_object* v_a_2073_, lean_object* v_b_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v_a_2091_; lean_object* v___y_2095_; lean_object* v___x_2097_; 
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_2089_ = lean_st_mk_ref(v___x_2088_);
lean_inc(v_a_2085_);
lean_inc_ref(v_a_2084_);
lean_inc(v_a_2083_);
lean_inc_ref(v_a_2082_);
lean_inc_ref(v_a_2073_);
v___x_2097_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_a_2073_, v___x_2089_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2099_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref(v___x_2097_);
lean_inc(v_a_2085_);
lean_inc_ref(v_a_2084_);
lean_inc(v_a_2083_);
lean_inc_ref(v_a_2082_);
lean_inc_ref(v_b_2074_);
v___x_2099_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_b_2074_, v___x_2089_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref(v___x_2099_);
lean_inc(v_a_2098_);
v___x_2101_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_2098_);
lean_inc(v_a_2100_);
v___x_2102_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_2100_);
v___x_2103_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_2101_, v___x_2102_);
lean_dec(v___x_2102_);
lean_dec(v___x_2101_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; 
lean_dec(v_a_2100_);
lean_dec(v_a_2098_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec(v_a_2076_);
lean_dec_ref(v_b_2074_);
lean_dec_ref(v_a_2073_);
v___x_2104_ = lean_box(0);
v_a_2091_ = v___x_2104_;
goto v___jp_2090_;
}
else
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2107_; lean_object* v_vars_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref(v___x_2105_);
v___x_2107_ = lean_st_ref_get(v___x_2089_);
v_vars_2108_ = lean_ctor_get(v___x_2107_, 1);
lean_inc_ref(v_vars_2108_);
lean_dec(v___x_2107_);
v___x_2109_ = lean_array_get_size(v_vars_2108_);
v___x_2110_ = lean_nat_dec_lt(v___x_2087_, v___x_2109_);
if (v___x_2110_ == 0)
{
lean_object* v_type_2111_; lean_object* v_zero_2112_; lean_object* v___f_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec_ref(v_vars_2108_);
v_type_2111_ = lean_ctor_get(v_a_2106_, 2);
v_zero_2112_ = lean_ctor_get(v_a_2106_, 13);
v___f_2113_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0));
lean_inc_ref(v_zero_2112_);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_zero_2112_);
lean_inc(v_a_2085_);
lean_inc_ref(v_a_2084_);
lean_inc(v_a_2083_);
lean_inc_ref(v_a_2082_);
lean_inc_ref(v_type_2111_);
v___x_2115_ = l_Lean_RArray_toExpr___redArg(v_type_2111_, v___f_2113_, v___x_2114_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2117_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
v___x_2117_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v_a_2073_, v_b_2074_, v_a_2106_, v_a_2098_, v_a_2100_, v_a_2116_, v___x_2089_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
v___y_2095_ = v___x_2117_;
goto v___jp_2094_;
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec(v_a_2106_);
lean_dec(v_a_2100_);
lean_dec(v_a_2098_);
lean_dec(v___x_2089_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec(v_a_2076_);
lean_dec_ref(v_b_2074_);
lean_dec_ref(v_a_2073_);
v_a_2118_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2115_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2115_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
else
{
lean_object* v_type_2126_; lean_object* v___f_2127_; lean_object* v___f_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v_type_2126_ = lean_ctor_get(v_a_2106_, 2);
v___f_2127_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0));
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3___boxed), 2, 1);
lean_closure_set(v___f_2128_, 0, v_vars_2108_);
v___x_2129_ = l_Lean_RArray_ofFn___redArg(v___x_2109_, v___f_2128_);
lean_inc(v_a_2085_);
lean_inc_ref(v_a_2084_);
lean_inc(v_a_2083_);
lean_inc_ref(v_a_2082_);
lean_inc_ref(v_type_2126_);
v___x_2130_ = l_Lean_RArray_toExpr___redArg(v_type_2126_, v___f_2127_, v___x_2129_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref(v___x_2130_);
v___x_2132_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v_a_2073_, v_b_2074_, v_a_2106_, v_a_2098_, v_a_2100_, v_a_2131_, v___x_2089_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
v___y_2095_ = v___x_2132_;
goto v___jp_2094_;
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_a_2106_);
lean_dec(v_a_2100_);
lean_dec(v_a_2098_);
lean_dec(v___x_2089_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec(v_a_2076_);
lean_dec_ref(v_b_2074_);
lean_dec_ref(v_a_2073_);
v_a_2133_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2130_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2130_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
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
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec(v_a_2100_);
lean_dec(v_a_2098_);
lean_dec(v___x_2089_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec(v_a_2076_);
lean_dec_ref(v_b_2074_);
lean_dec_ref(v_a_2073_);
v_a_2141_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2105_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2105_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec(v_a_2098_);
lean_dec(v___x_2089_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec(v_a_2076_);
lean_dec_ref(v_b_2074_);
lean_dec_ref(v_a_2073_);
v_a_2149_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2099_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2099_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v___x_2089_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec(v_a_2076_);
lean_dec_ref(v_b_2074_);
lean_dec_ref(v_a_2073_);
v_a_2157_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2097_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2097_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
v___jp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = lean_st_ref_get(v___x_2089_);
lean_dec(v___x_2089_);
lean_dec(v___x_2092_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_a_2091_);
return v___x_2093_;
}
v___jp_2094_:
{
if (lean_obj_tag(v___y_2095_) == 0)
{
lean_object* v_a_2096_; 
v_a_2096_ = lean_ctor_get(v___y_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref(v___y_2095_);
v_a_2091_ = v_a_2096_;
goto v___jp_2090_;
}
else
{
lean_dec(v___x_2089_);
return v___y_2095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___boxed(lean_object* v_a_2165_, lean_object* v_b_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_2165_, v_b_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
lean_dec(v_a_2167_);
return v_res_2179_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_OfNatModule(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_NatModuleNorm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_RArray(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_NatModuleNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* initialize_Init_Grind_Module_OfNatModule(uint8_t builtin);
lean_object* initialize_Init_Grind_Module_NatModuleNorm(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Lean_Data_RArray(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module_NatModuleNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
}
#ifdef __cplusplus
}
#endif
