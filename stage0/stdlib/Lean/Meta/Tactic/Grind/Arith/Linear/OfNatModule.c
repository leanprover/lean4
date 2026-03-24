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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc(v_a_3_);
v___x_14_ = lean_apply_12(v_x_2_, v_natStructId_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg___boxed(lean_object* v_natStructId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg(v_natStructId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_a_18_);
lean_dec(v_a_17_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(lean_object* v_00_u03b1_29_, lean_object* v_natStructId_30_, lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
lean_inc(v_a_41_);
lean_inc_ref(v_a_40_);
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
lean_inc(v_a_32_);
v___x_43_ = lean_apply_12(v_x_31_, v_natStructId_30_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___boxed(lean_object* v_00_u03b1_44_, lean_object* v_natStructId_45_, lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(v_00_u03b1_44_, v_natStructId_45_, v_x_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec(v_a_47_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; 
lean_inc(v_a_59_);
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
lean_dec(v_a_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNatStructId(lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
lean_inc(v_a_65_);
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
lean_dec(v_a_78_);
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
lean_inc(v_a_294_);
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
lean_dec(v_a_301_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(lean_object* v_f_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___f_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
lean_inc(v_a_306_);
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
lean_dec(v_a_322_);
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
size_t v_x_867__boxed_392_; lean_object* v_res_393_; 
v_x_867__boxed_392_ = lean_unbox_usize(v_x_390_);
lean_dec(v_x_390_);
v_res_393_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_389_, v_x_867__boxed_392_, v_x_391_);
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
size_t v_x_996__boxed_473_; lean_object* v_res_474_; 
v_x_996__boxed_473_ = lean_unbox_usize(v_x_471_);
lean_dec(v_x_471_);
v_res_474_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(v_00_u03b2_469_, v_x_470_, v_x_996__boxed_473_, v_x_472_);
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
size_t v_x_8225__boxed_699_; size_t v_x_8226__boxed_700_; lean_object* v_res_701_; 
v_x_8225__boxed_699_ = lean_unbox_usize(v_x_695_);
lean_dec(v_x_695_);
v_x_8226__boxed_700_ = lean_unbox_usize(v_x_696_);
lean_dec(v_x_696_);
v_res_701_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_694_, v_x_8225__boxed_699_, v_x_8226__boxed_700_, v_x_697_, v_x_698_);
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
lean_inc(v_a_710_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___lam__0___boxed(lean_object* v_e_728_, lean_object* v_a_729_, lean_object* v_s_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___lam__0(v_e_728_, v_a_729_, v_s_730_);
lean_dec(v_a_729_);
return v_res_731_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__1(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__0));
v___x_734_ = l_Lean_stringToMessageData(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(lean_object* v_e_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(v_e_735_, v_a_737_, v_a_745_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref(v___x_751_);
if (lean_obj_tag(v_a_752_) == 1)
{
lean_object* v_val_753_; uint8_t v___x_754_; 
v_val_753_ = lean_ctor_get(v_a_752_, 0);
lean_inc(v_val_753_);
lean_dec_ref(v_a_752_);
v___x_754_ = lean_nat_dec_eq(v_val_753_, v_a_736_);
lean_dec(v_val_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_739_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; uint8_t v_verbose_757_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref(v___x_755_);
v_verbose_757_ = lean_ctor_get_uint8(v_a_756_, sizeof(void*)*11 + 15);
lean_dec(v_a_756_);
if (v_verbose_757_ == 0)
{
lean_dec_ref(v_e_735_);
goto v___jp_748_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_758_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___closed__1);
v___x_759_ = l_Lean_indentExpr(v_e_735_);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_Meta_Grind_reportIssue(v___x_760_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_dec_ref(v___x_761_);
goto v___jp_748_;
}
else
{
return v___x_761_;
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v_e_735_);
v_a_762_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_755_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_755_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
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
lean_dec_ref(v_e_735_);
goto v___jp_748_;
}
}
else
{
lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec(v_a_752_);
lean_inc(v_a_736_);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_770_, 0, v_e_735_);
lean_closure_set(v___f_770_, 1, v_a_736_);
v___x_771_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_772_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_771_, v___f_770_, v_a_737_);
return v___x_772_;
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v_e_735_);
v_a_773_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_751_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_751_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
v___jp_748_:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_box(0);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___boxed(lean_object* v_e_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(v_e_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec(v_a_783_);
lean_dec(v_a_782_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_x_796_, v_x_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(lean_object* v_00_u03b2_800_, lean_object* v_x_801_, size_t v_x_802_, size_t v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_801_, v_x_802_, v_x_803_, v_x_804_, v_x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
size_t v_x_8497__boxed_813_; size_t v_x_8498__boxed_814_; lean_object* v_res_815_; 
v_x_8497__boxed_813_ = lean_unbox_usize(v_x_809_);
lean_dec(v_x_809_);
v_x_8498__boxed_814_ = lean_unbox_usize(v_x_810_);
lean_dec(v_x_810_);
v_res_815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(v_00_u03b2_807_, v_x_808_, v_x_8497__boxed_813_, v_x_8498__boxed_814_, v_x_811_, v_x_812_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_816_, lean_object* v_n_817_, lean_object* v_k_818_, lean_object* v_v_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(v_n_817_, v_k_818_, v_v_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_821_, size_t v_depth_822_, lean_object* v_keys_823_, lean_object* v_vals_824_, lean_object* v_heq_825_, lean_object* v_i_826_, lean_object* v_entries_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_822_, v_keys_823_, v_vals_824_, v_i_826_, v_entries_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_829_, lean_object* v_depth_830_, lean_object* v_keys_831_, lean_object* v_vals_832_, lean_object* v_heq_833_, lean_object* v_i_834_, lean_object* v_entries_835_){
_start:
{
size_t v_depth_boxed_836_; lean_object* v_res_837_; 
v_depth_boxed_836_ = lean_unbox_usize(v_depth_830_);
lean_dec(v_depth_830_);
v_res_837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(v_00_u03b2_829_, v_depth_boxed_836_, v_keys_831_, v_vals_832_, v_heq_833_, v_i_834_, v_entries_835_);
lean_dec_ref(v_vals_832_);
lean_dec_ref(v_keys_831_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_838_, lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_839_, v_x_840_, v_x_841_, v_x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(lean_object* v_a_844_, lean_object* v_e_845_, lean_object* v___x_846_, lean_object* v_s_847_){
_start:
{
lean_object* v_structs_848_; lean_object* v_typeIdOf_849_; lean_object* v_exprToStructId_850_; lean_object* v_exprToStructIdEntries_851_; lean_object* v_forbiddenNatModules_852_; lean_object* v_natStructs_853_; lean_object* v_natTypeIdOf_854_; lean_object* v_exprToNatStructId_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_structs_848_ = lean_ctor_get(v_s_847_, 0);
v_typeIdOf_849_ = lean_ctor_get(v_s_847_, 1);
v_exprToStructId_850_ = lean_ctor_get(v_s_847_, 2);
v_exprToStructIdEntries_851_ = lean_ctor_get(v_s_847_, 3);
v_forbiddenNatModules_852_ = lean_ctor_get(v_s_847_, 4);
v_natStructs_853_ = lean_ctor_get(v_s_847_, 5);
v_natTypeIdOf_854_ = lean_ctor_get(v_s_847_, 6);
v_exprToNatStructId_855_ = lean_ctor_get(v_s_847_, 7);
v___x_856_ = lean_array_get_size(v_natStructs_853_);
v___x_857_ = lean_nat_dec_lt(v_a_844_, v___x_856_);
if (v___x_857_ == 0)
{
lean_dec_ref(v___x_846_);
lean_dec_ref(v_e_845_);
return v_s_847_;
}
else
{
lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_894_; 
lean_inc_ref(v_exprToNatStructId_855_);
lean_inc_ref(v_natTypeIdOf_854_);
lean_inc_ref(v_natStructs_853_);
lean_inc_ref(v_forbiddenNatModules_852_);
lean_inc_ref(v_exprToStructIdEntries_851_);
lean_inc_ref(v_exprToStructId_850_);
lean_inc_ref(v_typeIdOf_849_);
lean_inc_ref(v_structs_848_);
v_isSharedCheck_894_ = !lean_is_exclusive(v_s_847_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; lean_object* v_unused_896_; lean_object* v_unused_897_; lean_object* v_unused_898_; lean_object* v_unused_899_; lean_object* v_unused_900_; lean_object* v_unused_901_; lean_object* v_unused_902_; 
v_unused_895_ = lean_ctor_get(v_s_847_, 7);
lean_dec(v_unused_895_);
v_unused_896_ = lean_ctor_get(v_s_847_, 6);
lean_dec(v_unused_896_);
v_unused_897_ = lean_ctor_get(v_s_847_, 5);
lean_dec(v_unused_897_);
v_unused_898_ = lean_ctor_get(v_s_847_, 4);
lean_dec(v_unused_898_);
v_unused_899_ = lean_ctor_get(v_s_847_, 3);
lean_dec(v_unused_899_);
v_unused_900_ = lean_ctor_get(v_s_847_, 2);
lean_dec(v_unused_900_);
v_unused_901_ = lean_ctor_get(v_s_847_, 1);
lean_dec(v_unused_901_);
v_unused_902_ = lean_ctor_get(v_s_847_, 0);
lean_dec(v_unused_902_);
v___x_859_ = v_s_847_;
v_isShared_860_ = v_isSharedCheck_894_;
goto v_resetjp_858_;
}
else
{
lean_dec(v_s_847_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_894_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v_v_861_; lean_object* v_id_862_; lean_object* v_structId_863_; lean_object* v_type_864_; lean_object* v_u_865_; lean_object* v_natModuleInst_866_; lean_object* v_leInst_x3f_867_; lean_object* v_ltInst_x3f_868_; lean_object* v_lawfulOrderLTInst_x3f_869_; lean_object* v_isPreorderInst_x3f_870_; lean_object* v_orderedAddInst_x3f_871_; lean_object* v_isLinearInst_x3f_872_; lean_object* v_addRightCancelInst_x3f_873_; lean_object* v_rfl__q_874_; lean_object* v_zero_875_; lean_object* v_toQFn_876_; lean_object* v_addFn_877_; lean_object* v_smulFn_878_; lean_object* v_termMap_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_893_; 
v_v_861_ = lean_array_fget(v_natStructs_853_, v_a_844_);
v_id_862_ = lean_ctor_get(v_v_861_, 0);
v_structId_863_ = lean_ctor_get(v_v_861_, 1);
v_type_864_ = lean_ctor_get(v_v_861_, 2);
v_u_865_ = lean_ctor_get(v_v_861_, 3);
v_natModuleInst_866_ = lean_ctor_get(v_v_861_, 4);
v_leInst_x3f_867_ = lean_ctor_get(v_v_861_, 5);
v_ltInst_x3f_868_ = lean_ctor_get(v_v_861_, 6);
v_lawfulOrderLTInst_x3f_869_ = lean_ctor_get(v_v_861_, 7);
v_isPreorderInst_x3f_870_ = lean_ctor_get(v_v_861_, 8);
v_orderedAddInst_x3f_871_ = lean_ctor_get(v_v_861_, 9);
v_isLinearInst_x3f_872_ = lean_ctor_get(v_v_861_, 10);
v_addRightCancelInst_x3f_873_ = lean_ctor_get(v_v_861_, 11);
v_rfl__q_874_ = lean_ctor_get(v_v_861_, 12);
v_zero_875_ = lean_ctor_get(v_v_861_, 13);
v_toQFn_876_ = lean_ctor_get(v_v_861_, 14);
v_addFn_877_ = lean_ctor_get(v_v_861_, 15);
v_smulFn_878_ = lean_ctor_get(v_v_861_, 16);
v_termMap_879_ = lean_ctor_get(v_v_861_, 17);
v_isSharedCheck_893_ = !lean_is_exclusive(v_v_861_);
if (v_isSharedCheck_893_ == 0)
{
v___x_881_ = v_v_861_;
v_isShared_882_ = v_isSharedCheck_893_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_termMap_879_);
lean_inc(v_smulFn_878_);
lean_inc(v_addFn_877_);
lean_inc(v_toQFn_876_);
lean_inc(v_zero_875_);
lean_inc(v_rfl__q_874_);
lean_inc(v_addRightCancelInst_x3f_873_);
lean_inc(v_isLinearInst_x3f_872_);
lean_inc(v_orderedAddInst_x3f_871_);
lean_inc(v_isPreorderInst_x3f_870_);
lean_inc(v_lawfulOrderLTInst_x3f_869_);
lean_inc(v_ltInst_x3f_868_);
lean_inc(v_leInst_x3f_867_);
lean_inc(v_natModuleInst_866_);
lean_inc(v_u_865_);
lean_inc(v_type_864_);
lean_inc(v_structId_863_);
lean_inc(v_id_862_);
lean_dec(v_v_861_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_893_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v_xs_x27_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_883_ = lean_box(0);
v_xs_x27_884_ = lean_array_fset(v_natStructs_853_, v_a_844_, v___x_883_);
v___x_885_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_879_, v_e_845_, v___x_846_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 17, v___x_885_);
v___x_887_ = v___x_881_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_id_862_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_structId_863_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_type_864_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_u_865_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v_natModuleInst_866_);
lean_ctor_set(v_reuseFailAlloc_892_, 5, v_leInst_x3f_867_);
lean_ctor_set(v_reuseFailAlloc_892_, 6, v_ltInst_x3f_868_);
lean_ctor_set(v_reuseFailAlloc_892_, 7, v_lawfulOrderLTInst_x3f_869_);
lean_ctor_set(v_reuseFailAlloc_892_, 8, v_isPreorderInst_x3f_870_);
lean_ctor_set(v_reuseFailAlloc_892_, 9, v_orderedAddInst_x3f_871_);
lean_ctor_set(v_reuseFailAlloc_892_, 10, v_isLinearInst_x3f_872_);
lean_ctor_set(v_reuseFailAlloc_892_, 11, v_addRightCancelInst_x3f_873_);
lean_ctor_set(v_reuseFailAlloc_892_, 12, v_rfl__q_874_);
lean_ctor_set(v_reuseFailAlloc_892_, 13, v_zero_875_);
lean_ctor_set(v_reuseFailAlloc_892_, 14, v_toQFn_876_);
lean_ctor_set(v_reuseFailAlloc_892_, 15, v_addFn_877_);
lean_ctor_set(v_reuseFailAlloc_892_, 16, v_smulFn_878_);
lean_ctor_set(v_reuseFailAlloc_892_, 17, v___x_885_);
v___x_887_ = v_reuseFailAlloc_892_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = lean_array_fset(v_xs_x27_884_, v_a_844_, v___x_887_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 5, v___x_888_);
v___x_890_ = v___x_859_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_structs_848_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_typeIdOf_849_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_exprToStructId_850_);
lean_ctor_set(v_reuseFailAlloc_891_, 3, v_exprToStructIdEntries_851_);
lean_ctor_set(v_reuseFailAlloc_891_, 4, v_forbiddenNatModules_852_);
lean_ctor_set(v_reuseFailAlloc_891_, 5, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_891_, 6, v_natTypeIdOf_854_);
lean_ctor_set(v_reuseFailAlloc_891_, 7, v_exprToNatStructId_855_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed(lean_object* v_a_903_, lean_object* v_e_904_, lean_object* v___x_905_, lean_object* v_s_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(v_a_903_, v_e_904_, v___x_905_, v_s_906_);
lean_dec(v_a_903_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(lean_object* v_e_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_994_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_994_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_994_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_994_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_termMap_926_; lean_object* v___x_927_; 
v_termMap_926_ = lean_ctor_get(v_a_922_, 17);
lean_inc_ref(v_termMap_926_);
lean_dec(v_a_922_);
v___x_927_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_926_, v_e_908_);
if (lean_obj_tag(v___x_927_) == 1)
{
lean_object* v_val_928_; lean_object* v___x_930_; 
lean_dec_ref(v_e_908_);
v_val_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_val_928_);
lean_dec_ref(v___x_927_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v_val_928_);
v___x_930_ = v___x_924_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_val_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
else
{
lean_object* v___x_932_; 
lean_dec(v___x_927_);
lean_del_object(v___x_924_);
v___x_932_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v_rfl__q_934_; lean_object* v_toQFn_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref(v___x_932_);
v_rfl__q_934_ = lean_ctor_get(v_a_933_, 12);
lean_inc_ref(v_rfl__q_934_);
v_toQFn_935_ = lean_ctor_get(v_a_933_, 14);
lean_inc_ref(v_toQFn_935_);
lean_dec(v_a_933_);
lean_inc_ref(v_e_908_);
v___x_936_ = l_Lean_Expr_app___override(v_toQFn_935_, v_e_908_);
v___x_937_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_936_, v_a_915_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___f_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref(v___x_937_);
lean_inc(v_a_938_);
v___x_939_ = l_Lean_Expr_app___override(v_rfl__q_934_, v_a_938_);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v_a_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
lean_inc_ref(v___x_940_);
lean_inc_ref(v_e_908_);
lean_inc(v_a_909_);
v___f_941_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed), 4, 3);
lean_closure_set(v___f_941_, 0, v_a_909_);
lean_closure_set(v___f_941_, 1, v_e_908_);
lean_closure_set(v___f_941_, 2, v___x_940_);
v___x_942_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_943_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_942_, v___f_941_, v_a_910_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v___x_944_; 
lean_dec_ref(v___x_943_);
lean_inc_ref(v_e_908_);
v___x_944_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(v_e_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v___x_945_; 
lean_dec_ref(v___x_944_);
v___x_945_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_942_, v_e_908_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v___x_945_, 0);
lean_dec(v_unused_953_);
v___x_947_ = v___x_945_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_dec(v___x_945_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_940_);
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_940_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref(v___x_940_);
v_a_954_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_945_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_945_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec_ref(v___x_940_);
lean_dec_ref(v_e_908_);
v_a_962_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_944_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_944_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec_ref(v___x_940_);
lean_dec_ref(v_e_908_);
v_a_970_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_943_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_943_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref(v_rfl__q_934_);
lean_dec_ref(v_e_908_);
v_a_978_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_937_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_937_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec_ref(v_e_908_);
v_a_986_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_932_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_932_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec_ref(v_e_908_);
v_a_995_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_921_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_921_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___boxed(lean_object* v_e_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec(v_a_1004_);
return v_res_1016_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(lean_object* v_natStruct_1017_, lean_object* v_inst_1018_){
_start:
{
lean_object* v_addFn_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v_addFn_1019_ = lean_ctor_get(v_natStruct_1017_, 15);
v___x_1020_ = l_Lean_Expr_appArg_x21(v_addFn_1019_);
v___x_1021_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1020_, v_inst_1018_);
lean_dec_ref(v___x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(lean_object* v_natStruct_1022_, lean_object* v_inst_1023_){
_start:
{
uint8_t v_res_1024_; lean_object* v_r_1025_; 
v_res_1024_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_natStruct_1022_, v_inst_1023_);
lean_dec_ref(v_inst_1023_);
lean_dec_ref(v_natStruct_1022_);
v_r_1025_ = lean_box(v_res_1024_);
return v_r_1025_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(lean_object* v_natStruct_1026_, lean_object* v_inst_1027_){
_start:
{
lean_object* v_zero_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v_zero_1028_ = lean_ctor_get(v_natStruct_1026_, 13);
v___x_1029_ = l_Lean_Expr_appArg_x21(v_zero_1028_);
v___x_1030_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1029_, v_inst_1027_);
lean_dec_ref(v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(lean_object* v_natStruct_1031_, lean_object* v_inst_1032_){
_start:
{
uint8_t v_res_1033_; lean_object* v_r_1034_; 
v_res_1033_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_natStruct_1031_, v_inst_1032_);
lean_dec_ref(v_inst_1032_);
lean_dec_ref(v_natStruct_1031_);
v_r_1034_ = lean_box(v_res_1033_);
return v_r_1034_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(lean_object* v_natStruct_1035_, lean_object* v_inst_1036_){
_start:
{
lean_object* v_smulFn_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_smulFn_1037_ = lean_ctor_get(v_natStruct_1035_, 16);
v___x_1038_ = l_Lean_Expr_appArg_x21(v_smulFn_1037_);
v___x_1039_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1038_, v_inst_1036_);
lean_dec_ref(v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst___boxed(lean_object* v_natStruct_1040_, lean_object* v_inst_1041_){
_start:
{
uint8_t v_res_1042_; lean_object* v_r_1043_; 
v_res_1042_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_natStruct_1040_, v_inst_1041_);
lean_dec_ref(v_inst_1041_);
lean_dec_ref(v_natStruct_1040_);
v_r_1043_ = lean_box(v_res_1042_);
return v_r_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(lean_object* v_e_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1104_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref(v___x_1102_);
v___x_1104_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1106_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref(v___x_1104_);
lean_inc_ref(v_e_1089_);
v___x_1106_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1089_, v_a_1098_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1257_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1257_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1257_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = l_Lean_Expr_cleanupAnnotations(v_a_1107_);
v___x_1112_ = l_Lean_Expr_isApp(v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
lean_dec_ref(v___x_1111_);
lean_del_object(v___x_1109_);
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
v___x_1113_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1113_;
}
else
{
lean_object* v_arg_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_arg_1114_ = lean_ctor_get(v___x_1111_, 1);
lean_inc_ref(v_arg_1114_);
v___x_1115_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1111_);
v___x_1116_ = l_Lean_Expr_isApp(v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_arg_1114_);
lean_del_object(v___x_1109_);
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
v___x_1117_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1117_;
}
else
{
lean_object* v_arg_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v_arg_1118_ = lean_ctor_get(v___x_1115_, 1);
lean_inc_ref(v_arg_1118_);
v___x_1119_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1115_);
v___x_1120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2));
v___x_1121_ = l_Lean_Expr_isConstOf(v___x_1119_, v___x_1120_);
if (v___x_1121_ == 0)
{
uint8_t v___x_1122_; 
lean_del_object(v___x_1109_);
v___x_1122_ = l_Lean_Expr_isApp(v___x_1119_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec_ref(v___x_1119_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1114_);
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
v___x_1123_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1123_;
}
else
{
lean_object* v_arg_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v_arg_1124_ = lean_ctor_get(v___x_1119_, 1);
lean_inc_ref(v_arg_1124_);
v___x_1125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1119_);
v___x_1126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5));
v___x_1127_ = l_Lean_Expr_isConstOf(v___x_1125_, v___x_1126_);
if (v___x_1127_ == 0)
{
uint8_t v___x_1128_; 
v___x_1128_ = l_Lean_Expr_isApp(v___x_1125_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
lean_dec_ref(v___x_1125_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1114_);
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
v___x_1129_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1125_);
v___x_1131_ = l_Lean_Expr_isApp(v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref(v___x_1130_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1114_);
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
v___x_1132_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1130_);
v___x_1134_ = l_Lean_Expr_isApp(v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_dec_ref(v___x_1133_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1114_);
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
v___x_1135_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1136_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1133_);
v___x_1137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8));
v___x_1138_ = l_Lean_Expr_isConstOf(v___x_1136_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11));
v___x_1140_ = l_Lean_Expr_isConstOf(v___x_1136_, v___x_1139_);
lean_dec_ref(v___x_1136_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1114_);
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
v___x_1141_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1141_;
}
else
{
uint8_t v___x_1142_; 
v___x_1142_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1105_, v_arg_1124_);
lean_dec_ref(v_arg_1124_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1114_);
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
v___x_1143_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; 
lean_dec_ref(v_e_1089_);
lean_inc_ref(v_arg_1118_);
v___x_1144_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1118_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v_fst_1146_; lean_object* v_snd_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1181_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref(v___x_1144_);
v_fst_1146_ = lean_ctor_get(v_a_1145_, 0);
v_snd_1147_ = lean_ctor_get(v_a_1145_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_a_1145_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1149_ = v_a_1145_;
v_isShared_1150_ = v_isSharedCheck_1181_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_snd_1147_);
lean_inc(v_fst_1146_);
lean_dec(v_a_1145_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1181_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; 
lean_inc_ref(v_arg_1114_);
v___x_1151_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1114_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1180_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1180_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1180_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_fst_1156_; lean_object* v_snd_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1179_; 
v_fst_1156_ = lean_ctor_get(v_a_1152_, 0);
v_snd_1157_ = lean_ctor_get(v_a_1152_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_a_1152_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1159_ = v_a_1152_;
v_isShared_1160_ = v_isSharedCheck_1179_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snd_1157_);
lean_inc(v_fst_1156_);
lean_dec(v_a_1152_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1179_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_addFn_1161_; lean_object* v_type_1162_; lean_object* v_u_1163_; lean_object* v_natModuleInst_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v_addFn_1161_ = lean_ctor_get(v_a_1103_, 22);
lean_inc_ref(v_addFn_1161_);
lean_dec(v_a_1103_);
v_type_1162_ = lean_ctor_get(v_a_1105_, 2);
lean_inc_ref(v_type_1162_);
v_u_1163_ = lean_ctor_get(v_a_1105_, 3);
lean_inc(v_u_1163_);
v_natModuleInst_1164_ = lean_ctor_get(v_a_1105_, 4);
lean_inc_ref(v_natModuleInst_1164_);
lean_dec(v_a_1105_);
lean_inc(v_fst_1156_);
lean_inc(v_fst_1146_);
v___x_1165_ = l_Lean_mkAppB(v_addFn_1161_, v_fst_1146_, v_fst_1156_);
v___x_1166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17));
v___x_1167_ = lean_box(0);
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 1);
lean_ctor_set(v___x_1149_, 1, v___x_1167_);
lean_ctor_set(v___x_1149_, 0, v_u_1163_);
v___x_1169_ = v___x_1149_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_u_1163_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1170_ = l_Lean_mkConst(v___x_1166_, v___x_1169_);
v___x_1171_ = l_Lean_mkApp8(v___x_1170_, v_type_1162_, v_natModuleInst_1164_, v_arg_1118_, v_arg_1114_, v_fst_1146_, v_fst_1156_, v_snd_1147_, v_snd_1157_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v___x_1171_);
lean_ctor_set(v___x_1159_, 0, v___x_1165_);
v___x_1173_ = v___x_1159_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1175_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1173_);
v___x_1175_ = v___x_1154_;
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
}
}
else
{
lean_del_object(v___x_1149_);
lean_dec(v_snd_1147_);
lean_dec(v_fst_1146_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1114_);
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
return v___x_1151_;
}
}
}
else
{
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1114_);
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
return v___x_1144_;
}
}
}
}
else
{
uint8_t v___x_1182_; 
lean_dec_ref(v___x_1136_);
v___x_1182_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_1105_, v_arg_1124_);
lean_dec_ref(v_arg_1124_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1114_);
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
v___x_1183_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; 
lean_dec_ref(v_e_1089_);
lean_inc_ref(v_arg_1114_);
v___x_1184_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_1114_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1211_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1211_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1211_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v_fst_1189_; lean_object* v_snd_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1210_; 
v_fst_1189_ = lean_ctor_get(v_a_1185_, 0);
v_snd_1190_ = lean_ctor_get(v_a_1185_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_a_1185_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1192_ = v_a_1185_;
v_isShared_1193_ = v_isSharedCheck_1210_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_snd_1190_);
lean_inc(v_fst_1189_);
lean_dec(v_a_1185_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1210_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_nsmulFn_1194_; lean_object* v_type_1195_; lean_object* v_u_1196_; lean_object* v_natModuleInst_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v_nsmulFn_1194_ = lean_ctor_get(v_a_1103_, 24);
lean_inc_ref(v_nsmulFn_1194_);
lean_dec(v_a_1103_);
v_type_1195_ = lean_ctor_get(v_a_1105_, 2);
lean_inc_ref(v_type_1195_);
v_u_1196_ = lean_ctor_get(v_a_1105_, 3);
lean_inc(v_u_1196_);
v_natModuleInst_1197_ = lean_ctor_get(v_a_1105_, 4);
lean_inc_ref(v_natModuleInst_1197_);
lean_dec(v_a_1105_);
lean_inc(v_fst_1189_);
lean_inc_ref(v_arg_1118_);
v___x_1198_ = l_Lean_mkAppB(v_nsmulFn_1194_, v_arg_1118_, v_fst_1189_);
v___x_1199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19));
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1201_, 0, v_u_1196_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = l_Lean_mkConst(v___x_1199_, v___x_1201_);
v___x_1203_ = l_Lean_mkApp6(v___x_1202_, v_type_1195_, v_natModuleInst_1197_, v_arg_1118_, v_arg_1114_, v_fst_1189_, v_snd_1190_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___x_1203_);
lean_ctor_set(v___x_1192_, 0, v___x_1198_);
v___x_1205_ = v___x_1192_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1205_);
v___x_1207_ = v___x_1187_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1114_);
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
return v___x_1184_;
}
}
}
}
}
}
}
else
{
lean_object* v_type_1212_; lean_object* v_u_1213_; lean_object* v_natModuleInst_1214_; lean_object* v_zero_1215_; lean_object* v___x_1216_; 
lean_dec_ref(v___x_1125_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1114_);
v_type_1212_ = lean_ctor_get(v_a_1105_, 2);
lean_inc_ref(v_type_1212_);
v_u_1213_ = lean_ctor_get(v_a_1105_, 3);
lean_inc(v_u_1213_);
v_natModuleInst_1214_ = lean_ctor_get(v_a_1105_, 4);
lean_inc_ref(v_natModuleInst_1214_);
v_zero_1215_ = lean_ctor_get(v_a_1105_, 13);
lean_inc_ref(v_zero_1215_);
lean_dec(v_a_1105_);
lean_inc_ref(v_e_1089_);
v___x_1216_ = l_Lean_Meta_isDefEqD(v_e_1089_, v_zero_1215_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1233_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1233_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1233_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
uint8_t v___x_1221_; 
v___x_1221_ = lean_unbox(v_a_1217_);
lean_dec(v_a_1217_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; 
lean_del_object(v___x_1219_);
lean_dec_ref(v_natModuleInst_1214_);
lean_dec(v_u_1213_);
lean_dec_ref(v_type_1212_);
lean_dec(v_a_1103_);
v___x_1222_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1222_;
}
else
{
lean_object* v_zero_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
lean_dec_ref(v_e_1089_);
v_zero_1223_ = lean_ctor_get(v_a_1103_, 17);
lean_inc_ref(v_zero_1223_);
lean_dec(v_a_1103_);
v___x_1224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21));
v___x_1225_ = lean_box(0);
v___x_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1226_, 0, v_u_1213_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = l_Lean_mkConst(v___x_1224_, v___x_1226_);
v___x_1228_ = l_Lean_mkAppB(v___x_1227_, v_type_1212_, v_natModuleInst_1214_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_zero_1223_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1229_);
v___x_1231_ = v___x_1219_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec_ref(v_natModuleInst_1214_);
lean_dec(v_u_1213_);
lean_dec_ref(v_type_1212_);
lean_dec(v_a_1103_);
lean_dec_ref(v_e_1089_);
v_a_1234_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1216_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1216_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
}
else
{
uint8_t v___x_1242_; 
lean_dec_ref(v___x_1119_);
lean_dec_ref(v_arg_1118_);
v___x_1242_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_1105_, v_arg_1114_);
lean_dec_ref(v_arg_1114_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
lean_del_object(v___x_1109_);
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
v___x_1243_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1243_;
}
else
{
lean_object* v_zero_1244_; lean_object* v_type_1245_; lean_object* v_u_1246_; lean_object* v_natModuleInst_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_dec_ref(v_e_1089_);
v_zero_1244_ = lean_ctor_get(v_a_1103_, 17);
lean_inc_ref(v_zero_1244_);
lean_dec(v_a_1103_);
v_type_1245_ = lean_ctor_get(v_a_1105_, 2);
lean_inc_ref(v_type_1245_);
v_u_1246_ = lean_ctor_get(v_a_1105_, 3);
lean_inc(v_u_1246_);
v_natModuleInst_1247_ = lean_ctor_get(v_a_1105_, 4);
lean_inc_ref(v_natModuleInst_1247_);
lean_dec(v_a_1105_);
v___x_1248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21));
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_u_1246_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = l_Lean_mkConst(v___x_1248_, v___x_1250_);
v___x_1252_ = l_Lean_mkAppB(v___x_1251_, v_type_1245_, v_natModuleInst_1247_);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v_zero_1244_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1253_);
v___x_1255_ = v___x_1109_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v_a_1105_);
lean_dec(v_a_1103_);
lean_dec_ref(v_e_1089_);
v_a_1258_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1106_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1106_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_a_1103_);
lean_dec_ref(v_e_1089_);
v_a_1266_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1104_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1104_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref(v_e_1089_);
v_a_1274_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1102_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1102_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___boxed(lean_object* v_e_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec(v_a_1283_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(lean_object* v___y_1296_, lean_object* v_e_1297_, lean_object* v_____x_1298_, lean_object* v_s_1299_){
_start:
{
lean_object* v_structs_1300_; lean_object* v_typeIdOf_1301_; lean_object* v_exprToStructId_1302_; lean_object* v_exprToStructIdEntries_1303_; lean_object* v_forbiddenNatModules_1304_; lean_object* v_natStructs_1305_; lean_object* v_natTypeIdOf_1306_; lean_object* v_exprToNatStructId_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_structs_1300_ = lean_ctor_get(v_s_1299_, 0);
v_typeIdOf_1301_ = lean_ctor_get(v_s_1299_, 1);
v_exprToStructId_1302_ = lean_ctor_get(v_s_1299_, 2);
v_exprToStructIdEntries_1303_ = lean_ctor_get(v_s_1299_, 3);
v_forbiddenNatModules_1304_ = lean_ctor_get(v_s_1299_, 4);
v_natStructs_1305_ = lean_ctor_get(v_s_1299_, 5);
v_natTypeIdOf_1306_ = lean_ctor_get(v_s_1299_, 6);
v_exprToNatStructId_1307_ = lean_ctor_get(v_s_1299_, 7);
v___x_1308_ = lean_array_get_size(v_natStructs_1305_);
v___x_1309_ = lean_nat_dec_lt(v___y_1296_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_dec_ref(v_____x_1298_);
lean_dec_ref(v_e_1297_);
return v_s_1299_;
}
else
{
lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1346_; 
lean_inc_ref(v_exprToNatStructId_1307_);
lean_inc_ref(v_natTypeIdOf_1306_);
lean_inc_ref(v_natStructs_1305_);
lean_inc_ref(v_forbiddenNatModules_1304_);
lean_inc_ref(v_exprToStructIdEntries_1303_);
lean_inc_ref(v_exprToStructId_1302_);
lean_inc_ref(v_typeIdOf_1301_);
lean_inc_ref(v_structs_1300_);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_s_1299_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; lean_object* v_unused_1348_; lean_object* v_unused_1349_; lean_object* v_unused_1350_; lean_object* v_unused_1351_; lean_object* v_unused_1352_; lean_object* v_unused_1353_; lean_object* v_unused_1354_; 
v_unused_1347_ = lean_ctor_get(v_s_1299_, 7);
lean_dec(v_unused_1347_);
v_unused_1348_ = lean_ctor_get(v_s_1299_, 6);
lean_dec(v_unused_1348_);
v_unused_1349_ = lean_ctor_get(v_s_1299_, 5);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v_s_1299_, 4);
lean_dec(v_unused_1350_);
v_unused_1351_ = lean_ctor_get(v_s_1299_, 3);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v_s_1299_, 2);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_s_1299_, 1);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_s_1299_, 0);
lean_dec(v_unused_1354_);
v___x_1311_ = v_s_1299_;
v_isShared_1312_ = v_isSharedCheck_1346_;
goto v_resetjp_1310_;
}
else
{
lean_dec(v_s_1299_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1346_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v_v_1313_; lean_object* v_id_1314_; lean_object* v_structId_1315_; lean_object* v_type_1316_; lean_object* v_u_1317_; lean_object* v_natModuleInst_1318_; lean_object* v_leInst_x3f_1319_; lean_object* v_ltInst_x3f_1320_; lean_object* v_lawfulOrderLTInst_x3f_1321_; lean_object* v_isPreorderInst_x3f_1322_; lean_object* v_orderedAddInst_x3f_1323_; lean_object* v_isLinearInst_x3f_1324_; lean_object* v_addRightCancelInst_x3f_1325_; lean_object* v_rfl__q_1326_; lean_object* v_zero_1327_; lean_object* v_toQFn_1328_; lean_object* v_addFn_1329_; lean_object* v_smulFn_1330_; lean_object* v_termMap_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1345_; 
v_v_1313_ = lean_array_fget(v_natStructs_1305_, v___y_1296_);
v_id_1314_ = lean_ctor_get(v_v_1313_, 0);
v_structId_1315_ = lean_ctor_get(v_v_1313_, 1);
v_type_1316_ = lean_ctor_get(v_v_1313_, 2);
v_u_1317_ = lean_ctor_get(v_v_1313_, 3);
v_natModuleInst_1318_ = lean_ctor_get(v_v_1313_, 4);
v_leInst_x3f_1319_ = lean_ctor_get(v_v_1313_, 5);
v_ltInst_x3f_1320_ = lean_ctor_get(v_v_1313_, 6);
v_lawfulOrderLTInst_x3f_1321_ = lean_ctor_get(v_v_1313_, 7);
v_isPreorderInst_x3f_1322_ = lean_ctor_get(v_v_1313_, 8);
v_orderedAddInst_x3f_1323_ = lean_ctor_get(v_v_1313_, 9);
v_isLinearInst_x3f_1324_ = lean_ctor_get(v_v_1313_, 10);
v_addRightCancelInst_x3f_1325_ = lean_ctor_get(v_v_1313_, 11);
v_rfl__q_1326_ = lean_ctor_get(v_v_1313_, 12);
v_zero_1327_ = lean_ctor_get(v_v_1313_, 13);
v_toQFn_1328_ = lean_ctor_get(v_v_1313_, 14);
v_addFn_1329_ = lean_ctor_get(v_v_1313_, 15);
v_smulFn_1330_ = lean_ctor_get(v_v_1313_, 16);
v_termMap_1331_ = lean_ctor_get(v_v_1313_, 17);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_v_1313_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1333_ = v_v_1313_;
v_isShared_1334_ = v_isSharedCheck_1345_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_termMap_1331_);
lean_inc(v_smulFn_1330_);
lean_inc(v_addFn_1329_);
lean_inc(v_toQFn_1328_);
lean_inc(v_zero_1327_);
lean_inc(v_rfl__q_1326_);
lean_inc(v_addRightCancelInst_x3f_1325_);
lean_inc(v_isLinearInst_x3f_1324_);
lean_inc(v_orderedAddInst_x3f_1323_);
lean_inc(v_isPreorderInst_x3f_1322_);
lean_inc(v_lawfulOrderLTInst_x3f_1321_);
lean_inc(v_ltInst_x3f_1320_);
lean_inc(v_leInst_x3f_1319_);
lean_inc(v_natModuleInst_1318_);
lean_inc(v_u_1317_);
lean_inc(v_type_1316_);
lean_inc(v_structId_1315_);
lean_inc(v_id_1314_);
lean_dec(v_v_1313_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1345_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v_xs_x27_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1335_ = lean_box(0);
v_xs_x27_1336_ = lean_array_fset(v_natStructs_1305_, v___y_1296_, v___x_1335_);
v___x_1337_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_1331_, v_e_1297_, v_____x_1298_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 17, v___x_1337_);
v___x_1339_ = v___x_1333_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_id_1314_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_structId_1315_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_type_1316_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v_u_1317_);
lean_ctor_set(v_reuseFailAlloc_1344_, 4, v_natModuleInst_1318_);
lean_ctor_set(v_reuseFailAlloc_1344_, 5, v_leInst_x3f_1319_);
lean_ctor_set(v_reuseFailAlloc_1344_, 6, v_ltInst_x3f_1320_);
lean_ctor_set(v_reuseFailAlloc_1344_, 7, v_lawfulOrderLTInst_x3f_1321_);
lean_ctor_set(v_reuseFailAlloc_1344_, 8, v_isPreorderInst_x3f_1322_);
lean_ctor_set(v_reuseFailAlloc_1344_, 9, v_orderedAddInst_x3f_1323_);
lean_ctor_set(v_reuseFailAlloc_1344_, 10, v_isLinearInst_x3f_1324_);
lean_ctor_set(v_reuseFailAlloc_1344_, 11, v_addRightCancelInst_x3f_1325_);
lean_ctor_set(v_reuseFailAlloc_1344_, 12, v_rfl__q_1326_);
lean_ctor_set(v_reuseFailAlloc_1344_, 13, v_zero_1327_);
lean_ctor_set(v_reuseFailAlloc_1344_, 14, v_toQFn_1328_);
lean_ctor_set(v_reuseFailAlloc_1344_, 15, v_addFn_1329_);
lean_ctor_set(v_reuseFailAlloc_1344_, 16, v_smulFn_1330_);
lean_ctor_set(v_reuseFailAlloc_1344_, 17, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1340_ = lean_array_fset(v_xs_x27_1336_, v___y_1296_, v___x_1339_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 5, v___x_1340_);
v___x_1342_ = v___x_1311_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_structs_1300_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_typeIdOf_1301_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_exprToStructId_1302_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_exprToStructIdEntries_1303_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_forbiddenNatModules_1304_);
lean_ctor_set(v_reuseFailAlloc_1343_, 5, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1343_, 6, v_natTypeIdOf_1306_);
lean_ctor_set(v_reuseFailAlloc_1343_, 7, v_exprToNatStructId_1307_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed(lean_object* v___y_1355_, lean_object* v_e_1356_, lean_object* v_____x_1357_, lean_object* v_s_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(v___y_1355_, v_e_1356_, v_____x_1357_, v_s_1358_);
lean_dec(v___y_1355_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule(lean_object* v_e_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_____x_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1463_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1463_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1463_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_termMap_1419_; lean_object* v___x_1420_; 
v_termMap_1419_ = lean_ctor_get(v_a_1415_, 17);
lean_inc_ref(v_termMap_1419_);
lean_dec(v_a_1415_);
v___x_1420_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_1419_, v_e_1360_);
if (lean_obj_tag(v___x_1420_) == 1)
{
lean_object* v_val_1421_; lean_object* v___x_1423_; 
lean_dec_ref(v_e_1360_);
v_val_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_val_1421_);
lean_dec_ref(v___x_1420_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v_val_1421_);
v___x_1423_ = v___x_1417_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_val_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
else
{
lean_object* v___x_1425_; 
lean_dec(v___x_1420_);
lean_del_object(v___x_1417_);
lean_inc_ref(v_e_1360_);
v___x_1425_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v_fst_1427_; lean_object* v_snd_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1462_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref(v___x_1425_);
v_fst_1427_ = lean_ctor_get(v_a_1426_, 0);
v_snd_1428_ = lean_ctor_get(v_a_1426_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_a_1426_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1430_ = v_a_1426_;
v_isShared_1431_ = v_isSharedCheck_1462_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_snd_1428_);
lean_inc(v_fst_1427_);
lean_dec(v_a_1426_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1462_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; 
lean_inc(v_a_1371_);
lean_inc_ref(v_a_1370_);
lean_inc(v_a_1369_);
lean_inc_ref(v_a_1368_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_a_1363_);
lean_inc(v_a_1362_);
v___x_1432_ = lean_grind_preprocess(v_fst_1427_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v_proof_x3f_1434_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref(v___x_1432_);
v_proof_x3f_1434_ = lean_ctor_get(v_a_1433_, 1);
if (lean_obj_tag(v_proof_x3f_1434_) == 1)
{
lean_object* v_expr_1435_; lean_object* v_val_1436_; lean_object* v___x_1437_; 
lean_inc_ref(v_proof_x3f_1434_);
v_expr_1435_ = lean_ctor_get(v_a_1433_, 0);
lean_inc_ref(v_expr_1435_);
lean_dec(v_a_1433_);
v_val_1436_ = lean_ctor_get(v_proof_x3f_1434_, 0);
lean_inc(v_val_1436_);
lean_dec_ref(v_proof_x3f_1434_);
v___x_1437_ = l_Lean_Meta_mkEqTrans(v_snd_1428_, v_val_1436_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref(v___x_1437_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 1, v_a_1438_);
lean_ctor_set(v___x_1430_, 0, v_expr_1435_);
v___x_1440_ = v___x_1430_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_expr_1435_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_a_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
v_____x_1374_ = v___x_1440_;
v___y_1375_ = v_a_1361_;
v___y_1376_ = v_a_1362_;
v___y_1377_ = v_a_1363_;
v___y_1378_ = v_a_1364_;
v___y_1379_ = v_a_1365_;
v___y_1380_ = v_a_1366_;
v___y_1381_ = v_a_1367_;
v___y_1382_ = v_a_1368_;
v___y_1383_ = v_a_1369_;
v___y_1384_ = v_a_1370_;
v___y_1385_ = v_a_1371_;
goto v___jp_1373_;
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec_ref(v_expr_1435_);
lean_del_object(v___x_1430_);
lean_dec_ref(v_e_1360_);
v_a_1442_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1437_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1437_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_object* v_expr_1450_; lean_object* v___x_1452_; 
v_expr_1450_ = lean_ctor_get(v_a_1433_, 0);
lean_inc_ref(v_expr_1450_);
lean_dec(v_a_1433_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v_expr_1450_);
v___x_1452_ = v___x_1430_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_expr_1450_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_snd_1428_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
v_____x_1374_ = v___x_1452_;
v___y_1375_ = v_a_1361_;
v___y_1376_ = v_a_1362_;
v___y_1377_ = v_a_1363_;
v___y_1378_ = v_a_1364_;
v___y_1379_ = v_a_1365_;
v___y_1380_ = v_a_1366_;
v___y_1381_ = v_a_1367_;
v___y_1382_ = v_a_1368_;
v___y_1383_ = v_a_1369_;
v___y_1384_ = v_a_1370_;
v___y_1385_ = v_a_1371_;
goto v___jp_1373_;
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_del_object(v___x_1430_);
lean_dec(v_snd_1428_);
lean_dec_ref(v_e_1360_);
v_a_1454_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1432_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1432_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1360_);
return v___x_1425_;
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec_ref(v_e_1360_);
v_a_1464_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1414_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1414_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
v___jp_1373_:
{
lean_object* v___x_1386_; 
lean_inc_ref(v_e_1360_);
v___x_1386_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(v_e_1360_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v___f_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref(v___x_1386_);
lean_inc_ref(v_____x_1374_);
lean_inc(v___y_1375_);
v___f_1387_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1387_, 0, v___y_1375_);
lean_closure_set(v___f_1387_, 1, v_e_1360_);
lean_closure_set(v___f_1387_, 2, v_____x_1374_);
v___x_1388_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1389_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1388_, v___f_1387_, v___y_1376_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; 
v_unused_1397_ = lean_ctor_get(v___x_1389_, 0);
lean_dec(v_unused_1397_);
v___x_1391_ = v___x_1389_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_dec(v___x_1389_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v_____x_1374_);
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_____x_1374_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v_____x_1374_);
v_a_1398_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1389_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1389_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec_ref(v_____x_1374_);
lean_dec_ref(v_e_1360_);
v_a_1406_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1386_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1386_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofNatModule___boxed(lean_object* v_e_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(v_e_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec(v_a_1474_);
lean_dec(v_a_1473_);
return v_res_1485_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = lean_box(0);
v___x_1487_ = lean_unsigned_to_nat(16u);
v___x_1488_ = lean_mk_array(v___x_1487_, v___x_1486_);
return v___x_1488_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0);
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
lean_ctor_set(v___x_1491_, 1, v___x_1489_);
return v___x_1491_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2));
v___x_1495_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
lean_ctor_set(v___x_1496_, 1, v___x_1494_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(lean_object* v_x_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_1511_ = lean_st_mk_ref(v___x_1510_);
lean_inc(v_a_1508_);
lean_inc_ref(v_a_1507_);
lean_inc(v_a_1506_);
lean_inc_ref(v_a_1505_);
lean_inc(v_a_1504_);
lean_inc_ref(v_a_1503_);
lean_inc(v_a_1502_);
lean_inc_ref(v_a_1501_);
lean_inc(v_a_1500_);
lean_inc(v_a_1499_);
lean_inc(v_a_1498_);
lean_inc(v___x_1511_);
v___x_1512_ = lean_apply_13(v_x_1497_, v___x_1511_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, lean_box(0));
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1521_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = lean_st_ref_get(v___x_1511_);
lean_dec(v___x_1511_);
lean_dec(v___x_1517_);
if (v_isShared_1516_ == 0)
{
v___x_1519_ = v___x_1515_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1513_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
else
{
lean_dec(v___x_1511_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___boxed(lean_object* v_x_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(v_x_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec(v_a_1523_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(lean_object* v_00_u03b1_1536_, lean_object* v_x_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_1551_ = lean_st_mk_ref(v___x_1550_);
lean_inc(v_a_1548_);
lean_inc_ref(v_a_1547_);
lean_inc(v_a_1546_);
lean_inc_ref(v_a_1545_);
lean_inc(v_a_1544_);
lean_inc_ref(v_a_1543_);
lean_inc(v_a_1542_);
lean_inc_ref(v_a_1541_);
lean_inc(v_a_1540_);
lean_inc(v_a_1539_);
lean_inc(v_a_1538_);
lean_inc(v___x_1551_);
v___x_1552_ = lean_apply_13(v_x_1537_, v___x_1551_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, lean_box(0));
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_st_ref_get(v___x_1551_);
lean_dec(v___x_1551_);
lean_dec(v___x_1557_);
if (v_isShared_1556_ == 0)
{
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1553_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
else
{
lean_dec(v___x_1551_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___boxed(lean_object* v_00_u03b1_1562_, lean_object* v_x_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(v_00_u03b1_1562_, v_x_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
lean_dec(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec(v_a_1564_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(lean_object* v_a_1577_, lean_object* v_b_1578_, lean_object* v_x_1579_){
_start:
{
if (lean_obj_tag(v_x_1579_) == 0)
{
lean_dec(v_b_1578_);
lean_dec_ref(v_a_1577_);
return v_x_1579_;
}
else
{
lean_object* v_key_1580_; lean_object* v_value_1581_; lean_object* v_tail_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1594_; 
v_key_1580_ = lean_ctor_get(v_x_1579_, 0);
v_value_1581_ = lean_ctor_get(v_x_1579_, 1);
v_tail_1582_ = lean_ctor_get(v_x_1579_, 2);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_x_1579_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1584_ = v_x_1579_;
v_isShared_1585_ = v_isSharedCheck_1594_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_tail_1582_);
lean_inc(v_value_1581_);
lean_inc(v_key_1580_);
lean_dec(v_x_1579_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1594_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
uint8_t v___x_1586_; 
v___x_1586_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_1580_, v_a_1577_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1587_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1577_, v_b_1578_, v_tail_1582_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 2, v___x_1587_);
v___x_1589_ = v___x_1584_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_key_1580_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_value_1581_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
else
{
lean_object* v___x_1592_; 
lean_dec(v_value_1581_);
lean_dec(v_key_1580_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 1, v_b_1578_);
lean_ctor_set(v___x_1584_, 0, v_a_1577_);
v___x_1592_ = v___x_1584_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1577_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_b_1578_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_tail_1582_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
if (lean_obj_tag(v_x_1596_) == 0)
{
return v_x_1595_;
}
else
{
lean_object* v_key_1597_; lean_object* v_value_1598_; lean_object* v_tail_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1622_; 
v_key_1597_ = lean_ctor_get(v_x_1596_, 0);
v_value_1598_ = lean_ctor_get(v_x_1596_, 1);
v_tail_1599_ = lean_ctor_get(v_x_1596_, 2);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_x_1596_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1601_ = v_x_1596_;
v_isShared_1602_ = v_isSharedCheck_1622_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_tail_1599_);
lean_inc(v_value_1598_);
lean_inc(v_key_1597_);
lean_dec(v_x_1596_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1622_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; uint64_t v___x_1604_; uint64_t v___x_1605_; uint64_t v___x_1606_; uint64_t v_fold_1607_; uint64_t v___x_1608_; uint64_t v___x_1609_; uint64_t v___x_1610_; size_t v___x_1611_; size_t v___x_1612_; size_t v___x_1613_; size_t v___x_1614_; size_t v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1603_ = lean_array_get_size(v_x_1595_);
v___x_1604_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_1597_);
v___x_1605_ = 32ULL;
v___x_1606_ = lean_uint64_shift_right(v___x_1604_, v___x_1605_);
v_fold_1607_ = lean_uint64_xor(v___x_1604_, v___x_1606_);
v___x_1608_ = 16ULL;
v___x_1609_ = lean_uint64_shift_right(v_fold_1607_, v___x_1608_);
v___x_1610_ = lean_uint64_xor(v_fold_1607_, v___x_1609_);
v___x_1611_ = lean_uint64_to_usize(v___x_1610_);
v___x_1612_ = lean_usize_of_nat(v___x_1603_);
v___x_1613_ = ((size_t)1ULL);
v___x_1614_ = lean_usize_sub(v___x_1612_, v___x_1613_);
v___x_1615_ = lean_usize_land(v___x_1611_, v___x_1614_);
v___x_1616_ = lean_array_uget_borrowed(v_x_1595_, v___x_1615_);
lean_inc(v___x_1616_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 2, v___x_1616_);
v___x_1618_ = v___x_1601_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_key_1597_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_value_1598_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_array_uset(v_x_1595_, v___x_1615_, v___x_1618_);
v_x_1595_ = v___x_1619_;
v_x_1596_ = v_tail_1599_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1623_, lean_object* v_source_1624_, lean_object* v_target_1625_){
_start:
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = lean_array_get_size(v_source_1624_);
v___x_1627_ = lean_nat_dec_lt(v_i_1623_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_dec_ref(v_source_1624_);
lean_dec(v_i_1623_);
return v_target_1625_;
}
else
{
lean_object* v_es_1628_; lean_object* v___x_1629_; lean_object* v_source_1630_; lean_object* v_target_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_es_1628_ = lean_array_fget(v_source_1624_, v_i_1623_);
v___x_1629_ = lean_box(0);
v_source_1630_ = lean_array_fset(v_source_1624_, v_i_1623_, v___x_1629_);
v_target_1631_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1625_, v_es_1628_);
v___x_1632_ = lean_unsigned_to_nat(1u);
v___x_1633_ = lean_nat_add(v_i_1623_, v___x_1632_);
lean_dec(v_i_1623_);
v_i_1623_ = v___x_1633_;
v_source_1624_ = v_source_1630_;
v_target_1625_ = v_target_1631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(lean_object* v_data_1635_){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v_nbuckets_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1636_ = lean_array_get_size(v_data_1635_);
v___x_1637_ = lean_unsigned_to_nat(2u);
v_nbuckets_1638_ = lean_nat_mul(v___x_1636_, v___x_1637_);
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = lean_box(0);
v___x_1641_ = lean_mk_array(v_nbuckets_1638_, v___x_1640_);
v___x_1642_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v___x_1639_, v_data_1635_, v___x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(lean_object* v_a_1643_, lean_object* v_x_1644_){
_start:
{
if (lean_obj_tag(v_x_1644_) == 0)
{
uint8_t v___x_1645_; 
v___x_1645_ = 0;
return v___x_1645_;
}
else
{
lean_object* v_key_1646_; lean_object* v_tail_1647_; uint8_t v___x_1648_; 
v_key_1646_ = lean_ctor_get(v_x_1644_, 0);
v_tail_1647_ = lean_ctor_get(v_x_1644_, 2);
v___x_1648_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_1646_, v_a_1643_);
if (v___x_1648_ == 0)
{
v_x_1644_ = v_tail_1647_;
goto _start;
}
else
{
return v___x_1648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg___boxed(lean_object* v_a_1650_, lean_object* v_x_1651_){
_start:
{
uint8_t v_res_1652_; lean_object* v_r_1653_; 
v_res_1652_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1650_, v_x_1651_);
lean_dec(v_x_1651_);
lean_dec_ref(v_a_1650_);
v_r_1653_ = lean_box(v_res_1652_);
return v_r_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(lean_object* v_m_1654_, lean_object* v_a_1655_, lean_object* v_b_1656_){
_start:
{
lean_object* v_size_1657_; lean_object* v_buckets_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1701_; 
v_size_1657_ = lean_ctor_get(v_m_1654_, 0);
v_buckets_1658_ = lean_ctor_get(v_m_1654_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_m_1654_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1660_ = v_m_1654_;
v_isShared_1661_ = v_isSharedCheck_1701_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_buckets_1658_);
lean_inc(v_size_1657_);
lean_dec(v_m_1654_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1701_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; uint64_t v___x_1663_; uint64_t v___x_1664_; uint64_t v___x_1665_; uint64_t v_fold_1666_; uint64_t v___x_1667_; uint64_t v___x_1668_; uint64_t v___x_1669_; size_t v___x_1670_; size_t v___x_1671_; size_t v___x_1672_; size_t v___x_1673_; size_t v___x_1674_; lean_object* v_bkt_1675_; uint8_t v___x_1676_; 
v___x_1662_ = lean_array_get_size(v_buckets_1658_);
v___x_1663_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_1655_);
v___x_1664_ = 32ULL;
v___x_1665_ = lean_uint64_shift_right(v___x_1663_, v___x_1664_);
v_fold_1666_ = lean_uint64_xor(v___x_1663_, v___x_1665_);
v___x_1667_ = 16ULL;
v___x_1668_ = lean_uint64_shift_right(v_fold_1666_, v___x_1667_);
v___x_1669_ = lean_uint64_xor(v_fold_1666_, v___x_1668_);
v___x_1670_ = lean_uint64_to_usize(v___x_1669_);
v___x_1671_ = lean_usize_of_nat(v___x_1662_);
v___x_1672_ = ((size_t)1ULL);
v___x_1673_ = lean_usize_sub(v___x_1671_, v___x_1672_);
v___x_1674_ = lean_usize_land(v___x_1670_, v___x_1673_);
v_bkt_1675_ = lean_array_uget_borrowed(v_buckets_1658_, v___x_1674_);
v___x_1676_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1655_, v_bkt_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v_size_x27_1678_; lean_object* v___x_1679_; lean_object* v_buckets_x27_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1677_ = lean_unsigned_to_nat(1u);
v_size_x27_1678_ = lean_nat_add(v_size_1657_, v___x_1677_);
lean_dec(v_size_1657_);
lean_inc(v_bkt_1675_);
v___x_1679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1679_, 0, v_a_1655_);
lean_ctor_set(v___x_1679_, 1, v_b_1656_);
lean_ctor_set(v___x_1679_, 2, v_bkt_1675_);
v_buckets_x27_1680_ = lean_array_uset(v_buckets_1658_, v___x_1674_, v___x_1679_);
v___x_1681_ = lean_unsigned_to_nat(4u);
v___x_1682_ = lean_nat_mul(v_size_x27_1678_, v___x_1681_);
v___x_1683_ = lean_unsigned_to_nat(3u);
v___x_1684_ = lean_nat_div(v___x_1682_, v___x_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_array_get_size(v_buckets_x27_1680_);
v___x_1686_ = lean_nat_dec_le(v___x_1684_, v___x_1685_);
lean_dec(v___x_1684_);
if (v___x_1686_ == 0)
{
lean_object* v_val_1687_; lean_object* v___x_1689_; 
v_val_1687_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_buckets_x27_1680_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 1, v_val_1687_);
lean_ctor_set(v___x_1660_, 0, v_size_x27_1678_);
v___x_1689_ = v___x_1660_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_size_x27_1678_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_val_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
else
{
lean_object* v___x_1692_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 1, v_buckets_x27_1680_);
lean_ctor_set(v___x_1660_, 0, v_size_x27_1678_);
v___x_1692_ = v___x_1660_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_size_x27_1678_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_buckets_x27_1680_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
else
{
lean_object* v___x_1694_; lean_object* v_buckets_x27_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
lean_inc(v_bkt_1675_);
v___x_1694_ = lean_box(0);
v_buckets_x27_1695_ = lean_array_uset(v_buckets_1658_, v___x_1674_, v___x_1694_);
v___x_1696_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1655_, v_b_1656_, v_bkt_1675_);
v___x_1697_ = lean_array_uset(v_buckets_x27_1695_, v___x_1674_, v___x_1696_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 1, v___x_1697_);
v___x_1699_ = v___x_1660_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_size_1657_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(lean_object* v_a_1702_, lean_object* v_x_1703_){
_start:
{
if (lean_obj_tag(v_x_1703_) == 0)
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_box(0);
return v___x_1704_;
}
else
{
lean_object* v_key_1705_; lean_object* v_value_1706_; lean_object* v_tail_1707_; uint8_t v___x_1708_; 
v_key_1705_ = lean_ctor_get(v_x_1703_, 0);
v_value_1706_ = lean_ctor_get(v_x_1703_, 1);
v_tail_1707_ = lean_ctor_get(v_x_1703_, 2);
v___x_1708_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_1705_, v_a_1702_);
if (v___x_1708_ == 0)
{
v_x_1703_ = v_tail_1707_;
goto _start;
}
else
{
lean_object* v___x_1710_; 
lean_inc(v_value_1706_);
v___x_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_value_1706_);
return v___x_1710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_1711_, lean_object* v_x_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1711_, v_x_1712_);
lean_dec(v_x_1712_);
lean_dec_ref(v_a_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(lean_object* v_m_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_buckets_1716_; lean_object* v___x_1717_; uint64_t v___x_1718_; uint64_t v___x_1719_; uint64_t v___x_1720_; uint64_t v_fold_1721_; uint64_t v___x_1722_; uint64_t v___x_1723_; uint64_t v___x_1724_; size_t v___x_1725_; size_t v___x_1726_; size_t v___x_1727_; size_t v___x_1728_; size_t v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_buckets_1716_ = lean_ctor_get(v_m_1714_, 1);
v___x_1717_ = lean_array_get_size(v_buckets_1716_);
v___x_1718_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_1715_);
v___x_1719_ = 32ULL;
v___x_1720_ = lean_uint64_shift_right(v___x_1718_, v___x_1719_);
v_fold_1721_ = lean_uint64_xor(v___x_1718_, v___x_1720_);
v___x_1722_ = 16ULL;
v___x_1723_ = lean_uint64_shift_right(v_fold_1721_, v___x_1722_);
v___x_1724_ = lean_uint64_xor(v_fold_1721_, v___x_1723_);
v___x_1725_ = lean_uint64_to_usize(v___x_1724_);
v___x_1726_ = lean_usize_of_nat(v___x_1717_);
v___x_1727_ = ((size_t)1ULL);
v___x_1728_ = lean_usize_sub(v___x_1726_, v___x_1727_);
v___x_1729_ = lean_usize_land(v___x_1725_, v___x_1728_);
v___x_1730_ = lean_array_uget_borrowed(v_buckets_1716_, v___x_1729_);
v___x_1731_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1715_, v___x_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg___boxed(lean_object* v_m_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_1732_, v_a_1733_);
lean_dec_ref(v_a_1733_);
lean_dec_ref(v_m_1732_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(lean_object* v_e_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v___x_1738_; lean_object* v_varMap_1739_; lean_object* v___x_1740_; 
v___x_1738_ = lean_st_ref_get(v_a_1736_);
v_varMap_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc_ref(v_varMap_1739_);
lean_dec(v___x_1738_);
v___x_1740_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_varMap_1739_, v_e_1735_);
lean_dec_ref(v_varMap_1739_);
if (lean_obj_tag(v___x_1740_) == 1)
{
lean_object* v_val_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v_e_1735_);
v_val_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1749_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_val_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1749_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_val_1741_);
v___x_1746_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
return v___x_1747_;
}
}
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v_vars_1752_; lean_object* v_varMap_1753_; lean_object* v_vars_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1767_; 
lean_dec(v___x_1740_);
v___x_1750_ = lean_st_ref_get(v_a_1736_);
v___x_1751_ = lean_st_ref_take(v_a_1736_);
v_vars_1752_ = lean_ctor_get(v___x_1750_, 1);
lean_inc_ref(v_vars_1752_);
lean_dec(v___x_1750_);
v_varMap_1753_ = lean_ctor_get(v___x_1751_, 0);
v_vars_1754_ = lean_ctor_get(v___x_1751_, 1);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1756_ = v___x_1751_;
v_isShared_1757_ = v_isSharedCheck_1767_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_vars_1754_);
lean_inc(v_varMap_1753_);
lean_dec(v___x_1751_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1767_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1758_ = lean_array_get_size(v_vars_1752_);
lean_dec_ref(v_vars_1752_);
lean_inc_ref(v_e_1735_);
v___x_1759_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_varMap_1753_, v_e_1735_, v___x_1758_);
v___x_1760_ = lean_array_push(v_vars_1754_, v_e_1735_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v___x_1760_);
lean_ctor_set(v___x_1756_, 0, v___x_1759_);
v___x_1762_ = v___x_1756_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = lean_st_ref_set(v_a_1736_, v___x_1762_);
v___x_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1758_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg___boxed(lean_object* v_e_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1768_, v_a_1769_);
lean_dec(v_a_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(lean_object* v_e_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1772_, v_a_1773_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___boxed(lean_object* v_e_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(v_e_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec(v_a_1788_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(lean_object* v_00_u03b2_1802_, lean_object* v_m_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_1803_, v_a_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___boxed(lean_object* v_00_u03b2_1806_, lean_object* v_m_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(v_00_u03b2_1806_, v_m_1807_, v_a_1808_);
lean_dec_ref(v_a_1808_);
lean_dec_ref(v_m_1807_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1(lean_object* v_00_u03b2_1810_, lean_object* v_m_1811_, lean_object* v_a_1812_, lean_object* v_b_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_m_1811_, v_a_1812_, v_b_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(lean_object* v_00_u03b2_1815_, lean_object* v_a_1816_, lean_object* v_x_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_1816_, v_x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1819_, lean_object* v_a_1820_, lean_object* v_x_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(v_00_u03b2_1819_, v_a_1820_, v_x_1821_);
lean_dec(v_x_1821_);
lean_dec_ref(v_a_1820_);
return v_res_1822_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(lean_object* v_00_u03b2_1823_, lean_object* v_a_1824_, lean_object* v_x_1825_){
_start:
{
uint8_t v___x_1826_; 
v___x_1826_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_1824_, v_x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1827_, lean_object* v_a_1828_, lean_object* v_x_1829_){
_start:
{
uint8_t v_res_1830_; lean_object* v_r_1831_; 
v_res_1830_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(v_00_u03b2_1827_, v_a_1828_, v_x_1829_);
lean_dec(v_x_1829_);
lean_dec_ref(v_a_1828_);
v_r_1831_ = lean_box(v_res_1830_);
return v_r_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3(lean_object* v_00_u03b2_1832_, lean_object* v_data_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_data_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4(lean_object* v_00_u03b2_1835_, lean_object* v_a_1836_, lean_object* v_b_1837_, lean_object* v_x_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_1836_, v_b_1837_, v_x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1840_, lean_object* v_i_1841_, lean_object* v_source_1842_, lean_object* v_target_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v_i_1841_, v_source_1842_, v_target_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1846_, v_x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(lean_object* v_e_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref(v___x_1863_);
lean_inc_ref(v_e_1849_);
v___x_1865_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1849_, v_a_1859_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1966_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1966_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1966_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = l_Lean_Expr_cleanupAnnotations(v_a_1866_);
v___x_1871_ = l_Lean_Expr_isApp(v___x_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1868_);
lean_dec(v_a_1864_);
v___x_1872_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1849_, v_a_1850_);
return v___x_1872_;
}
else
{
lean_object* v_arg_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v_arg_1873_ = lean_ctor_get(v___x_1870_, 1);
lean_inc_ref(v_arg_1873_);
v___x_1874_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1870_);
v___x_1875_ = l_Lean_Expr_isApp(v___x_1874_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; 
lean_dec_ref(v___x_1874_);
lean_dec_ref(v_arg_1873_);
lean_del_object(v___x_1868_);
lean_dec(v_a_1864_);
v___x_1876_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1849_, v_a_1850_);
return v___x_1876_;
}
else
{
lean_object* v_arg_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v_arg_1877_ = lean_ctor_get(v___x_1874_, 1);
lean_inc_ref(v_arg_1877_);
v___x_1878_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1874_);
v___x_1879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2));
v___x_1880_ = l_Lean_Expr_isConstOf(v___x_1878_, v___x_1879_);
if (v___x_1880_ == 0)
{
uint8_t v___x_1881_; 
lean_del_object(v___x_1868_);
v___x_1881_ = l_Lean_Expr_isApp(v___x_1878_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; 
lean_dec_ref(v___x_1878_);
lean_dec_ref(v_arg_1877_);
lean_dec_ref(v_arg_1873_);
lean_dec(v_a_1864_);
v___x_1882_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1849_, v_a_1850_);
return v___x_1882_;
}
else
{
lean_object* v_arg_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v_arg_1883_ = lean_ctor_get(v___x_1878_, 1);
lean_inc_ref(v_arg_1883_);
v___x_1884_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1878_);
v___x_1885_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5));
v___x_1886_ = l_Lean_Expr_isConstOf(v___x_1884_, v___x_1885_);
if (v___x_1886_ == 0)
{
uint8_t v___x_1887_; 
v___x_1887_ = l_Lean_Expr_isApp(v___x_1884_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; 
lean_dec_ref(v___x_1884_);
lean_dec_ref(v_arg_1883_);
lean_dec_ref(v_arg_1877_);
lean_dec_ref(v_arg_1873_);
lean_dec(v_a_1864_);
v___x_1888_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1849_, v_a_1850_);
return v___x_1888_;
}
else
{
lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1884_);
v___x_1890_ = l_Lean_Expr_isApp(v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; 
lean_dec_ref(v___x_1889_);
lean_dec_ref(v_arg_1883_);
lean_dec_ref(v_arg_1877_);
lean_dec_ref(v_arg_1873_);
lean_dec(v_a_1864_);
v___x_1891_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1849_, v_a_1850_);
return v___x_1891_;
}
else
{
lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1892_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1889_);
v___x_1893_ = l_Lean_Expr_isApp(v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; 
lean_dec_ref(v___x_1892_);
lean_dec_ref(v_arg_1883_);
lean_dec_ref(v_arg_1877_);
lean_dec_ref(v_arg_1873_);
lean_dec(v_a_1864_);
v___x_1894_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1849_, v_a_1850_);
return v___x_1894_;
}
else
{
lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1895_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1892_);
v___x_1896_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8));
v___x_1897_ = l_Lean_Expr_isConstOf(v___x_1895_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1898_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11));
v___x_1899_ = l_Lean_Expr_isConstOf(v___x_1895_, v___x_1898_);
lean_dec_ref(v___x_1895_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; 
lean_dec_ref(v_arg_1883_);
lean_dec_ref(v_arg_1877_);
lean_dec_ref(v_arg_1873_);
lean_dec(v_a_1864_);
v___x_1900_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1849_, v_a_1850_);
return v___x_1900_;
}
else
{
uint8_t v___x_1901_; 
v___x_1901_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_1864_, v_arg_1883_);
lean_dec_ref(v_arg_1883_);
lean_dec(v_a_1864_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; 
lean_dec_ref(v_arg_1877_);
lean_dec_ref(v_arg_1873_);
v___x_1902_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1849_, v_a_1850_);
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; 
lean_dec_ref(v_e_1849_);
v___x_1903_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_1877_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1905_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref(v___x_1903_);
v___x_1905_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_1873_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1914_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1914_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1914_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1910_, 0, v_a_1904_);
lean_ctor_set(v___x_1910_, 1, v_a_1906_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1910_);
v___x_1912_ = v___x_1908_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
else
{
lean_dec(v_a_1904_);
return v___x_1905_;
}
}
else
{
lean_dec_ref(v_arg_1873_);
return v___x_1903_;
}
}
}
}
else
{
uint8_t v___x_1915_; 
lean_dec_ref(v___x_1895_);
v___x_1915_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_1864_, v_arg_1883_);
lean_dec_ref(v_arg_1883_);
lean_dec(v_a_1864_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; 
lean_dec_ref(v_arg_1877_);
lean_dec_ref(v_arg_1873_);
v___x_1916_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1849_, v_a_1850_);
return v___x_1916_;
}
else
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_Meta_getNatValue_x3f(v_arg_1877_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
lean_dec_ref(v_arg_1877_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref(v___x_1917_);
if (lean_obj_tag(v_a_1918_) == 1)
{
lean_object* v_val_1919_; lean_object* v___x_1920_; 
lean_dec_ref(v_e_1849_);
v_val_1919_ = lean_ctor_get(v_a_1918_, 0);
lean_inc(v_val_1919_);
lean_dec_ref(v_a_1918_);
v___x_1920_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_1873_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1929_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1925_, 0, v_val_1919_);
lean_ctor_set(v___x_1925_, 1, v_a_1921_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
else
{
lean_dec(v_val_1919_);
return v___x_1920_;
}
}
else
{
lean_object* v___x_1930_; 
lean_dec(v_a_1918_);
lean_dec_ref(v_arg_1873_);
v___x_1930_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1849_, v_a_1850_);
return v___x_1930_;
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec_ref(v_arg_1873_);
lean_dec_ref(v_e_1849_);
v_a_1931_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1917_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1917_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
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
lean_object* v_zero_1939_; lean_object* v___x_1940_; 
lean_dec_ref(v___x_1884_);
lean_dec_ref(v_arg_1883_);
lean_dec_ref(v_arg_1877_);
lean_dec_ref(v_arg_1873_);
v_zero_1939_ = lean_ctor_get(v_a_1864_, 13);
lean_inc_ref(v_zero_1939_);
lean_dec(v_a_1864_);
lean_inc_ref(v_e_1849_);
v___x_1940_ = l_Lean_Meta_isDefEqD(v_e_1849_, v_zero_1939_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1951_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1951_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1951_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_unbox(v_a_1941_);
lean_dec(v_a_1941_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; 
lean_del_object(v___x_1943_);
v___x_1946_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1849_, v_a_1850_);
return v___x_1946_;
}
else
{
lean_object* v___x_1947_; lean_object* v___x_1949_; 
lean_dec_ref(v_e_1849_);
v___x_1947_ = lean_box(0);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1947_);
v___x_1949_ = v___x_1943_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v_e_1849_);
v_a_1952_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1940_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1940_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
else
{
uint8_t v___x_1960_; 
lean_dec_ref(v___x_1878_);
lean_dec_ref(v_arg_1877_);
v___x_1960_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_1864_, v_arg_1873_);
lean_dec_ref(v_arg_1873_);
lean_dec(v_a_1864_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; 
lean_del_object(v___x_1868_);
v___x_1961_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_1849_, v_a_1850_);
return v___x_1961_;
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1964_; 
lean_dec_ref(v_e_1849_);
v___x_1962_ = lean_box(0);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1962_);
v___x_1964_ = v___x_1868_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec(v_a_1864_);
lean_dec_ref(v_e_1849_);
v_a_1967_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1865_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1865_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v_e_1849_);
v_a_1975_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1863_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1863_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify___boxed(lean_object* v_e_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_e_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec(v_a_1984_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(lean_object* v_a_2005_, lean_object* v_b_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_ctx_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_Meta_Grind_mkDiseqProof(v_a_2005_, v_b_2006_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v_type_2026_; lean_object* v_u_2027_; lean_object* v_natModuleInst_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_2024_);
v_type_2026_ = lean_ctor_get(v_a_2007_, 2);
lean_inc_ref(v_type_2026_);
v_u_2027_ = lean_ctor_get(v_a_2007_, 3);
lean_inc(v_u_2027_);
v_natModuleInst_2028_ = lean_ctor_get(v_a_2007_, 4);
lean_inc_ref(v_natModuleInst_2028_);
lean_dec_ref(v_a_2007_);
v___x_2029_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2));
v___x_2030_ = lean_box(0);
v___x_2031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2031_, 0, v_u_2027_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = l_Lean_mkConst(v___x_2029_, v___x_2031_);
v___x_2033_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_2008_);
v___x_2034_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_2009_);
v___x_2035_ = l_Lean_eagerReflBoolTrue;
v___x_2036_ = l_Lean_mkApp6(v___x_2032_, v_type_2026_, v_natModuleInst_2028_, v_ctx_2010_, v___x_2033_, v___x_2034_, v___x_2035_);
v___x_2037_ = l_Lean_Expr_app___override(v_a_2025_, v___x_2036_);
v___x_2038_ = l_Lean_Meta_Grind_closeGoal(v___x_2037_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
return v___x_2038_;
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec_ref(v_ctx_2010_);
lean_dec(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
v_a_2039_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2024_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2024_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___boxed(lean_object** _args){
lean_object* v_a_2047_ = _args[0];
lean_object* v_b_2048_ = _args[1];
lean_object* v_a_2049_ = _args[2];
lean_object* v_a_2050_ = _args[3];
lean_object* v_a_2051_ = _args[4];
lean_object* v_ctx_2052_ = _args[5];
lean_object* v___y_2053_ = _args[6];
lean_object* v___y_2054_ = _args[7];
lean_object* v___y_2055_ = _args[8];
lean_object* v___y_2056_ = _args[9];
lean_object* v___y_2057_ = _args[10];
lean_object* v___y_2058_ = _args[11];
lean_object* v___y_2059_ = _args[12];
lean_object* v___y_2060_ = _args[13];
lean_object* v___y_2061_ = _args[14];
lean_object* v___y_2062_ = _args[15];
lean_object* v___y_2063_ = _args[16];
lean_object* v___y_2064_ = _args[17];
lean_object* v___y_2065_ = _args[18];
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v_a_2047_, v_b_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_ctx_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec(v___y_2053_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(lean_object* v___y_2067_){
_start:
{
lean_inc_ref(v___y_2067_);
return v___y_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed(lean_object* v___y_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(v___y_2068_);
lean_dec_ref(v___y_2068_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3(lean_object* v_vars_2070_, lean_object* v_x_2071_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = lean_array_fget_borrowed(v_vars_2070_, v_x_2071_);
lean_inc(v___x_2072_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3___boxed(lean_object* v_vars_2073_, lean_object* v_x_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3(v_vars_2073_, v_x_2074_);
lean_dec(v_x_2074_);
lean_dec_ref(v_vars_2073_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(lean_object* v_a_2077_, lean_object* v_b_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v_a_2095_; lean_object* v___y_2099_; lean_object* v___x_2101_; 
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
v___x_2093_ = lean_st_mk_ref(v___x_2092_);
lean_inc_ref(v_a_2077_);
v___x_2101_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_a_2077_, v___x_2093_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2103_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref(v___x_2101_);
lean_inc_ref(v_b_2078_);
v___x_2103_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_b_2078_, v___x_2093_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref(v___x_2103_);
lean_inc(v_a_2102_);
v___x_2105_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_2102_);
lean_inc(v_a_2104_);
v___x_2106_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_2104_);
v___x_2107_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_2105_, v___x_2106_);
lean_dec(v___x_2106_);
lean_dec(v___x_2105_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; 
lean_dec(v_a_2104_);
lean_dec(v_a_2102_);
lean_dec_ref(v_b_2078_);
lean_dec_ref(v_a_2077_);
v___x_2108_ = lean_box(0);
v_a_2095_ = v___x_2108_;
goto v___jp_2094_;
}
else
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; lean_object* v_vars_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref(v___x_2109_);
v___x_2111_ = lean_st_ref_get(v___x_2093_);
v_vars_2112_ = lean_ctor_get(v___x_2111_, 1);
lean_inc_ref(v_vars_2112_);
lean_dec(v___x_2111_);
v___x_2113_ = lean_array_get_size(v_vars_2112_);
v___x_2114_ = lean_nat_dec_lt(v___x_2091_, v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v_type_2115_; lean_object* v_zero_2116_; lean_object* v___f_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_dec_ref(v_vars_2112_);
v_type_2115_ = lean_ctor_get(v_a_2110_, 2);
v_zero_2116_ = lean_ctor_get(v_a_2110_, 13);
v___f_2117_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0));
lean_inc_ref(v_zero_2116_);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_zero_2116_);
lean_inc_ref(v_type_2115_);
v___x_2119_ = l_Lean_RArray_toExpr___redArg(v_type_2115_, v___f_2117_, v___x_2118_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2121_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref(v___x_2119_);
v___x_2121_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v_a_2077_, v_b_2078_, v_a_2110_, v_a_2102_, v_a_2104_, v_a_2120_, v___x_2093_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
v___y_2099_ = v___x_2121_;
goto v___jp_2098_;
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_a_2110_);
lean_dec(v_a_2104_);
lean_dec(v_a_2102_);
lean_dec(v___x_2093_);
lean_dec_ref(v_b_2078_);
lean_dec_ref(v_a_2077_);
v_a_2122_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2119_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2119_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v_type_2130_; lean_object* v___f_2131_; lean_object* v___f_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v_type_2130_ = lean_ctor_get(v_a_2110_, 2);
v___f_2131_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0));
v___f_2132_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3___boxed), 2, 1);
lean_closure_set(v___f_2132_, 0, v_vars_2112_);
v___x_2133_ = l_Lean_RArray_ofFn___redArg(v___x_2113_, v___f_2132_);
lean_inc_ref(v_type_2130_);
v___x_2134_ = l_Lean_RArray_toExpr___redArg(v_type_2130_, v___f_2131_, v___x_2133_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref(v___x_2134_);
v___x_2136_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v_a_2077_, v_b_2078_, v_a_2110_, v_a_2102_, v_a_2104_, v_a_2135_, v___x_2093_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
v___y_2099_ = v___x_2136_;
goto v___jp_2098_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_a_2110_);
lean_dec(v_a_2104_);
lean_dec(v_a_2102_);
lean_dec(v___x_2093_);
lean_dec_ref(v_b_2078_);
lean_dec_ref(v_a_2077_);
v_a_2137_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2134_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2134_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_a_2104_);
lean_dec(v_a_2102_);
lean_dec(v___x_2093_);
lean_dec_ref(v_b_2078_);
lean_dec_ref(v_a_2077_);
v_a_2145_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2109_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2109_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v_a_2102_);
lean_dec(v___x_2093_);
lean_dec_ref(v_b_2078_);
lean_dec_ref(v_a_2077_);
v_a_2153_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2103_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2103_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec(v___x_2093_);
lean_dec_ref(v_b_2078_);
lean_dec_ref(v_a_2077_);
v_a_2161_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2101_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2101_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
v___jp_2094_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = lean_st_ref_get(v___x_2093_);
lean_dec(v___x_2093_);
lean_dec(v___x_2096_);
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_a_2095_);
return v___x_2097_;
}
v___jp_2098_:
{
if (lean_obj_tag(v___y_2099_) == 0)
{
lean_object* v_a_2100_; 
v_a_2100_ = lean_ctor_get(v___y_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref(v___y_2099_);
v_a_2095_ = v_a_2100_;
goto v___jp_2094_;
}
else
{
lean_dec(v___x_2093_);
return v___y_2099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___boxed(lean_object* v_a_2169_, lean_object* v_b_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(v_a_2169_, v_b_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
lean_dec(v_a_2181_);
lean_dec_ref(v_a_2180_);
lean_dec(v_a_2179_);
lean_dec_ref(v_a_2178_);
lean_dec(v_a_2177_);
lean_dec_ref(v_a_2176_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
lean_dec(v_a_2173_);
lean_dec(v_a_2172_);
lean_dec(v_a_2171_);
return v_res_2183_;
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
