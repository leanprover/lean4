// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM public import Lean.Meta.Tactic.Grind.Arith.CommRing.MonadSemiring import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr public import Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "`grind` internal error, invalid semiringId"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "`grind` internal error, invalid ringId"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4_value),LEAN_SCALAR_PTR_LITERAL(232, 146, 236, 221, 122, 127, 105, 70)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "expression in two different semirings"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "`grind` failed to find instance"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM.0.Lean.Grind.CommRing.Expr.denoteAsRingExpr.go"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(lean_object* v_semiringId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
v___x_14_ = lean_apply_12(v_x_2_, v_semiringId_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg___boxed(lean_object* v_semiringId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(v_semiringId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(lean_object* v_00_u03b1_29_, lean_object* v_semiringId_30_, lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
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
v___x_43_ = lean_apply_12(v_x_31_, v_semiringId_30_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___boxed(lean_object* v_00_u03b1_44_, lean_object* v_semiringId_45_, lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(v_00_u03b1_44_, v_semiringId_45_, v_x_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; 
lean_inc(v_a_59_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_a_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg___boxed(lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(v_a_62_);
lean_dec(v_a_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
lean_inc(v_a_65_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v_a_65_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___boxed(lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(lean_object* v_e_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; 
lean_inc(v___y_102_);
lean_inc_ref(v___y_101_);
lean_inc(v___y_100_);
lean_inc_ref(v___y_99_);
lean_inc(v___y_98_);
lean_inc_ref(v___y_97_);
lean_inc(v___y_96_);
lean_inc_ref(v___y_95_);
lean_inc(v___y_94_);
lean_inc(v___y_93_);
v___x_104_ = lean_grind_canon(v_e_91_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_106_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref(v___x_104_);
v___x_106_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_105_, v___y_98_);
return v___x_106_;
}
else
{
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed(lean_object* v_e_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(v_e_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec(v___y_109_);
lean_dec(v___y_108_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(lean_object* v_e_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_e_121_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1___boxed(lean_object* v_e_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(v_e_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec(v___y_137_);
lean_dec(v___y_136_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(lean_object* v_msgData_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; lean_object* v_env_162_; lean_object* v___x_163_; lean_object* v_mctx_164_; lean_object* v_lctx_165_; lean_object* v_options_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_161_ = lean_st_ref_get(v___y_159_);
v_env_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc_ref(v_env_162_);
lean_dec(v___x_161_);
v___x_163_ = lean_st_ref_get(v___y_157_);
v_mctx_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc_ref(v_mctx_164_);
lean_dec(v___x_163_);
v_lctx_165_ = lean_ctor_get(v___y_156_, 2);
v_options_166_ = lean_ctor_get(v___y_158_, 2);
lean_inc_ref(v_options_166_);
lean_inc_ref(v_lctx_165_);
v___x_167_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_167_, 0, v_env_162_);
lean_ctor_set(v___x_167_, 1, v_mctx_164_);
lean_ctor_set(v___x_167_, 2, v_lctx_165_);
lean_ctor_set(v___x_167_, 3, v_options_166_);
v___x_168_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v_msgData_155_);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0___boxed(lean_object* v_msgData_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msgData_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(lean_object* v_msg_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_ref_183_; lean_object* v___x_184_; lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
v_ref_183_ = lean_ctor_get(v___y_180_, 5);
v___x_184_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msg_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_193_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
lean_inc(v_ref_183_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v_ref_183_);
lean_ctor_set(v___x_189_, 1, v_a_185_);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 1);
lean_ctor_set(v___x_187_, 0, v___x_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg___boxed(lean_object* v_msg_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_200_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0));
v___x_203_ = l_Lean_stringToMessageData(v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_205_, v_a_213_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_230_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_230_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_230_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_230_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_semirings_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_semirings_221_ = lean_ctor_get(v_a_217_, 3);
lean_inc_ref(v_semirings_221_);
lean_dec(v_a_217_);
v___x_222_ = lean_array_get_size(v_semirings_221_);
v___x_223_ = lean_nat_dec_lt(v_a_204_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec_ref(v_semirings_221_);
lean_del_object(v___x_219_);
v___x_224_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1);
v___x_225_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_224_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_array_fget(v_semirings_221_, v_a_204_);
lean_dec_ref(v_semirings_221_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_226_);
v___x_228_ = v___x_219_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
v_a_231_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_216_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_216_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed(lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec(v_a_240_);
lean_dec(v_a_239_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(lean_object* v_00_u03b1_252_, lean_object* v_msg_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_253_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___boxed(lean_object* v_00_u03b1_267_, lean_object* v_msg_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(v_00_u03b1_267_, v_msg_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec(v___y_270_);
lean_dec(v___y_269_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(lean_object* v_a_282_, lean_object* v_f_283_, lean_object* v_s_284_){
_start:
{
lean_object* v_rings_285_; lean_object* v_typeIdOf_286_; lean_object* v_exprToRingId_287_; lean_object* v_semirings_288_; lean_object* v_stypeIdOf_289_; lean_object* v_exprToSemiringId_290_; lean_object* v_ncRings_291_; lean_object* v_exprToNCRingId_292_; lean_object* v_nctypeIdOf_293_; lean_object* v_ncSemirings_294_; lean_object* v_exprToNCSemiringId_295_; lean_object* v_ncstypeIdOf_296_; lean_object* v_steps_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_rings_285_ = lean_ctor_get(v_s_284_, 0);
v_typeIdOf_286_ = lean_ctor_get(v_s_284_, 1);
v_exprToRingId_287_ = lean_ctor_get(v_s_284_, 2);
v_semirings_288_ = lean_ctor_get(v_s_284_, 3);
v_stypeIdOf_289_ = lean_ctor_get(v_s_284_, 4);
v_exprToSemiringId_290_ = lean_ctor_get(v_s_284_, 5);
v_ncRings_291_ = lean_ctor_get(v_s_284_, 6);
v_exprToNCRingId_292_ = lean_ctor_get(v_s_284_, 7);
v_nctypeIdOf_293_ = lean_ctor_get(v_s_284_, 8);
v_ncSemirings_294_ = lean_ctor_get(v_s_284_, 9);
v_exprToNCSemiringId_295_ = lean_ctor_get(v_s_284_, 10);
v_ncstypeIdOf_296_ = lean_ctor_get(v_s_284_, 11);
v_steps_297_ = lean_ctor_get(v_s_284_, 12);
v___x_298_ = lean_array_get_size(v_semirings_288_);
v___x_299_ = lean_nat_dec_lt(v_a_282_, v___x_298_);
if (v___x_299_ == 0)
{
lean_dec_ref(v_f_283_);
return v_s_284_;
}
else
{
lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_311_; 
lean_inc(v_steps_297_);
lean_inc_ref(v_ncstypeIdOf_296_);
lean_inc_ref(v_exprToNCSemiringId_295_);
lean_inc_ref(v_ncSemirings_294_);
lean_inc_ref(v_nctypeIdOf_293_);
lean_inc_ref(v_exprToNCRingId_292_);
lean_inc_ref(v_ncRings_291_);
lean_inc_ref(v_exprToSemiringId_290_);
lean_inc_ref(v_stypeIdOf_289_);
lean_inc_ref(v_semirings_288_);
lean_inc_ref(v_exprToRingId_287_);
lean_inc_ref(v_typeIdOf_286_);
lean_inc_ref(v_rings_285_);
v_isSharedCheck_311_ = !lean_is_exclusive(v_s_284_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; lean_object* v_unused_319_; lean_object* v_unused_320_; lean_object* v_unused_321_; lean_object* v_unused_322_; lean_object* v_unused_323_; lean_object* v_unused_324_; 
v_unused_312_ = lean_ctor_get(v_s_284_, 12);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_s_284_, 11);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_s_284_, 10);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_s_284_, 9);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_s_284_, 8);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_s_284_, 7);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_s_284_, 6);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_s_284_, 5);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_s_284_, 4);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_s_284_, 3);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_s_284_, 2);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_s_284_, 1);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_s_284_, 0);
lean_dec(v_unused_324_);
v___x_301_ = v_s_284_;
v_isShared_302_ = v_isSharedCheck_311_;
goto v_resetjp_300_;
}
else
{
lean_dec(v_s_284_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_311_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v_v_303_; lean_object* v___x_304_; lean_object* v_xs_x27_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v_v_303_ = lean_array_fget(v_semirings_288_, v_a_282_);
v___x_304_ = lean_box(0);
v_xs_x27_305_ = lean_array_fset(v_semirings_288_, v_a_282_, v___x_304_);
v___x_306_ = lean_apply_1(v_f_283_, v_v_303_);
v___x_307_ = lean_array_fset(v_xs_x27_305_, v_a_282_, v___x_306_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 3, v___x_307_);
v___x_309_ = v___x_301_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_rings_285_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_typeIdOf_286_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_exprToRingId_287_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_310_, 4, v_stypeIdOf_289_);
lean_ctor_set(v_reuseFailAlloc_310_, 5, v_exprToSemiringId_290_);
lean_ctor_set(v_reuseFailAlloc_310_, 6, v_ncRings_291_);
lean_ctor_set(v_reuseFailAlloc_310_, 7, v_exprToNCRingId_292_);
lean_ctor_set(v_reuseFailAlloc_310_, 8, v_nctypeIdOf_293_);
lean_ctor_set(v_reuseFailAlloc_310_, 9, v_ncSemirings_294_);
lean_ctor_set(v_reuseFailAlloc_310_, 10, v_exprToNCSemiringId_295_);
lean_ctor_set(v_reuseFailAlloc_310_, 11, v_ncstypeIdOf_296_);
lean_ctor_set(v_reuseFailAlloc_310_, 12, v_steps_297_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed(lean_object* v_a_325_, lean_object* v_f_326_, lean_object* v_s_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(v_a_325_, v_f_326_, v_s_327_);
lean_dec(v_a_325_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(lean_object* v_f_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___f_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
lean_inc(v_a_330_);
v___f_333_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_333_, 0, v_a_330_);
lean_closure_set(v___f_333_, 1, v_f_329_);
v___x_334_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_335_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_334_, v___f_333_, v_a_331_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___boxed(lean_object* v_f_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(v_f_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec(v_a_337_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(lean_object* v_f_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___f_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
lean_inc(v_a_342_);
v___f_354_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_354_, 0, v_a_342_);
lean_closure_set(v___f_354_, 1, v_f_341_);
v___x_355_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_356_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_355_, v___f_354_, v_a_343_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed(lean_object* v_f_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(v_f_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec(v_a_359_);
lean_dec(v_a_358_);
return v_res_370_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0));
v___x_373_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed), 12, 0);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM(void){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0));
v___x_378_ = l_Lean_stringToMessageData(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_380_, v_a_388_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_393_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref(v___x_391_);
v___x_393_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_408_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_408_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_408_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_408_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_ringId_398_; lean_object* v_rings_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_ringId_398_ = lean_ctor_get(v_a_394_, 1);
lean_inc(v_ringId_398_);
lean_dec(v_a_394_);
v_rings_399_ = lean_ctor_get(v_a_392_, 0);
lean_inc_ref(v_rings_399_);
lean_dec(v_a_392_);
v___x_400_ = lean_array_get_size(v_rings_399_);
v___x_401_ = lean_nat_dec_lt(v_ringId_398_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec_ref(v_rings_399_);
lean_dec(v_ringId_398_);
lean_del_object(v___x_396_);
v___x_402_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1);
v___x_403_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_402_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_array_fget(v_rings_399_, v_ringId_398_);
lean_dec(v_ringId_398_);
lean_dec_ref(v_rings_399_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_404_);
v___x_406_ = v___x_396_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec(v_a_392_);
v_a_409_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_393_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_393_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
v_a_417_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_391_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_391_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed(lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec(v_a_426_);
lean_dec(v_a_425_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(lean_object* v_ringId_438_, lean_object* v_f_439_, lean_object* v_s_440_){
_start:
{
lean_object* v_rings_441_; lean_object* v_typeIdOf_442_; lean_object* v_exprToRingId_443_; lean_object* v_semirings_444_; lean_object* v_stypeIdOf_445_; lean_object* v_exprToSemiringId_446_; lean_object* v_ncRings_447_; lean_object* v_exprToNCRingId_448_; lean_object* v_nctypeIdOf_449_; lean_object* v_ncSemirings_450_; lean_object* v_exprToNCSemiringId_451_; lean_object* v_ncstypeIdOf_452_; lean_object* v_steps_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_rings_441_ = lean_ctor_get(v_s_440_, 0);
v_typeIdOf_442_ = lean_ctor_get(v_s_440_, 1);
v_exprToRingId_443_ = lean_ctor_get(v_s_440_, 2);
v_semirings_444_ = lean_ctor_get(v_s_440_, 3);
v_stypeIdOf_445_ = lean_ctor_get(v_s_440_, 4);
v_exprToSemiringId_446_ = lean_ctor_get(v_s_440_, 5);
v_ncRings_447_ = lean_ctor_get(v_s_440_, 6);
v_exprToNCRingId_448_ = lean_ctor_get(v_s_440_, 7);
v_nctypeIdOf_449_ = lean_ctor_get(v_s_440_, 8);
v_ncSemirings_450_ = lean_ctor_get(v_s_440_, 9);
v_exprToNCSemiringId_451_ = lean_ctor_get(v_s_440_, 10);
v_ncstypeIdOf_452_ = lean_ctor_get(v_s_440_, 11);
v_steps_453_ = lean_ctor_get(v_s_440_, 12);
v___x_454_ = lean_array_get_size(v_rings_441_);
v___x_455_ = lean_nat_dec_lt(v_ringId_438_, v___x_454_);
if (v___x_455_ == 0)
{
lean_dec_ref(v_f_439_);
return v_s_440_;
}
else
{
lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_467_; 
lean_inc(v_steps_453_);
lean_inc_ref(v_ncstypeIdOf_452_);
lean_inc_ref(v_exprToNCSemiringId_451_);
lean_inc_ref(v_ncSemirings_450_);
lean_inc_ref(v_nctypeIdOf_449_);
lean_inc_ref(v_exprToNCRingId_448_);
lean_inc_ref(v_ncRings_447_);
lean_inc_ref(v_exprToSemiringId_446_);
lean_inc_ref(v_stypeIdOf_445_);
lean_inc_ref(v_semirings_444_);
lean_inc_ref(v_exprToRingId_443_);
lean_inc_ref(v_typeIdOf_442_);
lean_inc_ref(v_rings_441_);
v_isSharedCheck_467_ = !lean_is_exclusive(v_s_440_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; lean_object* v_unused_469_; lean_object* v_unused_470_; lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; lean_object* v_unused_479_; lean_object* v_unused_480_; 
v_unused_468_ = lean_ctor_get(v_s_440_, 12);
lean_dec(v_unused_468_);
v_unused_469_ = lean_ctor_get(v_s_440_, 11);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_s_440_, 10);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_s_440_, 9);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_s_440_, 8);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_s_440_, 7);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_s_440_, 6);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_s_440_, 5);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_s_440_, 4);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_s_440_, 3);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_s_440_, 2);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_s_440_, 1);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_s_440_, 0);
lean_dec(v_unused_480_);
v___x_457_ = v_s_440_;
v_isShared_458_ = v_isSharedCheck_467_;
goto v_resetjp_456_;
}
else
{
lean_dec(v_s_440_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_467_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v_v_459_; lean_object* v___x_460_; lean_object* v_xs_x27_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v_v_459_ = lean_array_fget(v_rings_441_, v_ringId_438_);
v___x_460_ = lean_box(0);
v_xs_x27_461_ = lean_array_fset(v_rings_441_, v_ringId_438_, v___x_460_);
v___x_462_ = lean_apply_1(v_f_439_, v_v_459_);
v___x_463_ = lean_array_fset(v_xs_x27_461_, v_ringId_438_, v___x_462_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_463_);
v___x_465_ = v___x_457_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_typeIdOf_442_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_exprToRingId_443_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_semirings_444_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v_stypeIdOf_445_);
lean_ctor_set(v_reuseFailAlloc_466_, 5, v_exprToSemiringId_446_);
lean_ctor_set(v_reuseFailAlloc_466_, 6, v_ncRings_447_);
lean_ctor_set(v_reuseFailAlloc_466_, 7, v_exprToNCRingId_448_);
lean_ctor_set(v_reuseFailAlloc_466_, 8, v_nctypeIdOf_449_);
lean_ctor_set(v_reuseFailAlloc_466_, 9, v_ncSemirings_450_);
lean_ctor_set(v_reuseFailAlloc_466_, 10, v_exprToNCSemiringId_451_);
lean_ctor_set(v_reuseFailAlloc_466_, 11, v_ncstypeIdOf_452_);
lean_ctor_set(v_reuseFailAlloc_466_, 12, v_steps_453_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed(lean_object* v_ringId_481_, lean_object* v_f_482_, lean_object* v_s_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(v_ringId_481_, v_f_482_, v_s_483_);
lean_dec(v_ringId_481_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(lean_object* v_f_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v_ringId_500_; lean_object* v___f_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref(v___x_498_);
v_ringId_500_ = lean_ctor_get(v_a_499_, 1);
lean_inc(v_ringId_500_);
lean_dec(v_a_499_);
v___f_501_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed), 3, 2);
lean_closure_set(v___f_501_, 0, v_ringId_500_);
lean_closure_set(v___f_501_, 1, v_f_485_);
v___x_502_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_503_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_502_, v___f_501_, v_a_487_);
return v___x_503_;
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec_ref(v_f_485_);
v_a_504_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_498_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_498_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed(lean_object* v_f_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v_f_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec(v_a_514_);
lean_dec(v_a_513_);
return v_res_525_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_527_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0));
v___x_528_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed), 12, 0);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v___x_527_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM(void){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0(lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_s_533_){
_start:
{
lean_object* v_rings_534_; lean_object* v_typeIdOf_535_; lean_object* v_exprToRingId_536_; lean_object* v_semirings_537_; lean_object* v_stypeIdOf_538_; lean_object* v_exprToSemiringId_539_; lean_object* v_ncRings_540_; lean_object* v_exprToNCRingId_541_; lean_object* v_nctypeIdOf_542_; lean_object* v_ncSemirings_543_; lean_object* v_exprToNCSemiringId_544_; lean_object* v_ncstypeIdOf_545_; lean_object* v_steps_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_rings_534_ = lean_ctor_get(v_s_533_, 0);
v_typeIdOf_535_ = lean_ctor_get(v_s_533_, 1);
v_exprToRingId_536_ = lean_ctor_get(v_s_533_, 2);
v_semirings_537_ = lean_ctor_get(v_s_533_, 3);
v_stypeIdOf_538_ = lean_ctor_get(v_s_533_, 4);
v_exprToSemiringId_539_ = lean_ctor_get(v_s_533_, 5);
v_ncRings_540_ = lean_ctor_get(v_s_533_, 6);
v_exprToNCRingId_541_ = lean_ctor_get(v_s_533_, 7);
v_nctypeIdOf_542_ = lean_ctor_get(v_s_533_, 8);
v_ncSemirings_543_ = lean_ctor_get(v_s_533_, 9);
v_exprToNCSemiringId_544_ = lean_ctor_get(v_s_533_, 10);
v_ncstypeIdOf_545_ = lean_ctor_get(v_s_533_, 11);
v_steps_546_ = lean_ctor_get(v_s_533_, 12);
v___x_547_ = lean_array_get_size(v_semirings_537_);
v___x_548_ = lean_nat_dec_lt(v_a_531_, v___x_547_);
if (v___x_548_ == 0)
{
lean_dec_ref(v_a_532_);
return v_s_533_;
}
else
{
lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_572_; 
lean_inc(v_steps_546_);
lean_inc_ref(v_ncstypeIdOf_545_);
lean_inc_ref(v_exprToNCSemiringId_544_);
lean_inc_ref(v_ncSemirings_543_);
lean_inc_ref(v_nctypeIdOf_542_);
lean_inc_ref(v_exprToNCRingId_541_);
lean_inc_ref(v_ncRings_540_);
lean_inc_ref(v_exprToSemiringId_539_);
lean_inc_ref(v_stypeIdOf_538_);
lean_inc_ref(v_semirings_537_);
lean_inc_ref(v_exprToRingId_536_);
lean_inc_ref(v_typeIdOf_535_);
lean_inc_ref(v_rings_534_);
v_isSharedCheck_572_ = !lean_is_exclusive(v_s_533_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; lean_object* v_unused_574_; lean_object* v_unused_575_; lean_object* v_unused_576_; lean_object* v_unused_577_; lean_object* v_unused_578_; lean_object* v_unused_579_; lean_object* v_unused_580_; lean_object* v_unused_581_; lean_object* v_unused_582_; lean_object* v_unused_583_; lean_object* v_unused_584_; lean_object* v_unused_585_; 
v_unused_573_ = lean_ctor_get(v_s_533_, 12);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_s_533_, 11);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_s_533_, 10);
lean_dec(v_unused_575_);
v_unused_576_ = lean_ctor_get(v_s_533_, 9);
lean_dec(v_unused_576_);
v_unused_577_ = lean_ctor_get(v_s_533_, 8);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_s_533_, 7);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_s_533_, 6);
lean_dec(v_unused_579_);
v_unused_580_ = lean_ctor_get(v_s_533_, 5);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_s_533_, 4);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_s_533_, 3);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_s_533_, 2);
lean_dec(v_unused_583_);
v_unused_584_ = lean_ctor_get(v_s_533_, 1);
lean_dec(v_unused_584_);
v_unused_585_ = lean_ctor_get(v_s_533_, 0);
lean_dec(v_unused_585_);
v___x_550_ = v_s_533_;
v_isShared_551_ = v_isSharedCheck_572_;
goto v_resetjp_549_;
}
else
{
lean_dec(v_s_533_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_572_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_v_552_; lean_object* v_toSemiring_553_; lean_object* v_ringId_554_; lean_object* v_commSemiringInst_555_; lean_object* v_addRightCancelInst_x3f_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_570_; 
v_v_552_ = lean_array_fget(v_semirings_537_, v_a_531_);
v_toSemiring_553_ = lean_ctor_get(v_v_552_, 0);
v_ringId_554_ = lean_ctor_get(v_v_552_, 1);
v_commSemiringInst_555_ = lean_ctor_get(v_v_552_, 2);
v_addRightCancelInst_x3f_556_ = lean_ctor_get(v_v_552_, 3);
v_isSharedCheck_570_ = !lean_is_exclusive(v_v_552_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; 
v_unused_571_ = lean_ctor_get(v_v_552_, 4);
lean_dec(v_unused_571_);
v___x_558_ = v_v_552_;
v_isShared_559_ = v_isSharedCheck_570_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_addRightCancelInst_x3f_556_);
lean_inc(v_commSemiringInst_555_);
lean_inc(v_ringId_554_);
lean_inc(v_toSemiring_553_);
lean_dec(v_v_552_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_570_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v_xs_x27_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_560_ = lean_box(0);
v_xs_x27_561_ = lean_array_fset(v_semirings_537_, v_a_531_, v___x_560_);
v___x_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_562_, 0, v_a_532_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 4, v___x_562_);
v___x_564_ = v___x_558_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_toSemiring_553_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_ringId_554_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_commSemiringInst_555_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_addRightCancelInst_x3f_556_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v___x_562_);
v___x_564_ = v_reuseFailAlloc_569_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = lean_array_fset(v_xs_x27_561_, v_a_531_, v___x_564_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 3, v___x_565_);
v___x_567_ = v___x_550_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_rings_534_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_typeIdOf_535_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_exprToRingId_536_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_stypeIdOf_538_);
lean_ctor_set(v_reuseFailAlloc_568_, 5, v_exprToSemiringId_539_);
lean_ctor_set(v_reuseFailAlloc_568_, 6, v_ncRings_540_);
lean_ctor_set(v_reuseFailAlloc_568_, 7, v_exprToNCRingId_541_);
lean_ctor_set(v_reuseFailAlloc_568_, 8, v_nctypeIdOf_542_);
lean_ctor_set(v_reuseFailAlloc_568_, 9, v_ncSemirings_543_);
lean_ctor_set(v_reuseFailAlloc_568_, 10, v_exprToNCSemiringId_544_);
lean_ctor_set(v_reuseFailAlloc_568_, 11, v_ncstypeIdOf_545_);
lean_ctor_set(v_reuseFailAlloc_568_, 12, v_steps_546_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0___boxed(lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_s_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0(v_a_586_, v_a_587_, v_s_588_);
lean_dec(v_a_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn(lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v___y_614_; lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_657_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_657_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_657_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_657_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_toQFn_x3f_640_; 
v_toQFn_x3f_640_ = lean_ctor_get(v_a_636_, 4);
if (lean_obj_tag(v_toQFn_x3f_640_) == 1)
{
lean_object* v_val_641_; lean_object* v___x_643_; 
lean_inc_ref(v_toQFn_x3f_640_);
lean_dec(v_a_636_);
v_val_641_ = lean_ctor_get(v_toQFn_x3f_640_, 0);
lean_inc(v_val_641_);
lean_dec_ref(v_toQFn_x3f_640_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v_val_641_);
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_val_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
else
{
lean_object* v_toSemiring_645_; lean_object* v_type_646_; lean_object* v_u_647_; lean_object* v_semiringInst_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_del_object(v___x_638_);
v_toSemiring_645_ = lean_ctor_get(v_a_636_, 0);
lean_inc_ref(v_toSemiring_645_);
lean_dec(v_a_636_);
v_type_646_ = lean_ctor_get(v_toSemiring_645_, 1);
lean_inc_ref(v_type_646_);
v_u_647_ = lean_ctor_get(v_toSemiring_645_, 2);
lean_inc(v_u_647_);
v_semiringInst_648_ = lean_ctor_get(v_toSemiring_645_, 3);
lean_inc_ref(v_semiringInst_648_);
lean_dec_ref(v_toSemiring_645_);
v___x_649_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5));
v___x_650_ = lean_box(0);
v___x_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_651_, 0, v_u_647_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = l_Lean_mkConst(v___x_649_, v___x_651_);
v___x_653_ = l_Lean_mkAppB(v___x_652_, v_type_646_, v_semiringInst_648_);
lean_inc(v_a_611_);
lean_inc_ref(v_a_610_);
lean_inc(v_a_609_);
lean_inc_ref(v_a_608_);
lean_inc(v_a_607_);
lean_inc_ref(v_a_606_);
lean_inc(v_a_605_);
lean_inc_ref(v_a_604_);
lean_inc(v_a_603_);
lean_inc(v_a_602_);
v___x_654_ = lean_grind_canon(v___x_653_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref(v___x_654_);
v___x_656_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_655_, v_a_607_);
v___y_614_ = v___x_656_;
goto v___jp_613_;
}
else
{
v___y_614_ = v___x_654_;
goto v___jp_613_;
}
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
v_a_658_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_635_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_635_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
v___jp_613_:
{
if (lean_obj_tag(v___y_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___f_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_a_615_ = lean_ctor_get(v___y_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref(v___y_614_);
lean_inc(v_a_615_);
lean_inc(v_a_601_);
v___f_616_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0___boxed), 3, 2);
lean_closure_set(v___f_616_, 0, v_a_601_);
lean_closure_set(v___f_616_, 1, v_a_615_);
v___x_617_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_618_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_617_, v___f_616_, v_a_602_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v___x_618_, 0);
lean_dec(v_unused_626_);
v___x_620_ = v___x_618_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_dec(v___x_618_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v_a_615_);
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_615_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v_a_615_);
v_a_627_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_618_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_618_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
else
{
return v___y_614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___boxed(lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec(v_a_667_);
lean_dec(v_a_666_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(lean_object* v_u_687_, lean_object* v_type_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_add_698_; lean_object* v___x_699_; 
v___x_694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1));
v___x_695_ = lean_box(0);
v___x_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_696_, 0, v_u_687_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
lean_inc_ref(v___x_696_);
v___x_697_ = l_Lean_mkConst(v___x_694_, v___x_696_);
lean_inc_ref(v_type_688_);
v_add_698_ = l_Lean_Expr_app___override(v___x_697_, v_type_688_);
v___x_699_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_add_698_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_713_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_713_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_713_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_713_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
if (lean_obj_tag(v_a_700_) == 1)
{
lean_object* v_val_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
lean_del_object(v___x_702_);
v_val_704_ = lean_ctor_get(v_a_700_, 0);
lean_inc(v_val_704_);
lean_dec_ref(v_a_700_);
v___x_705_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3));
v___x_706_ = l_Lean_mkConst(v___x_705_, v___x_696_);
v___x_707_ = l_Lean_mkAppB(v___x_706_, v_type_688_, v_val_704_);
v___x_708_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v___x_707_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
return v___x_708_;
}
else
{
lean_object* v___x_709_; lean_object* v___x_711_; 
lean_dec(v_a_700_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v_type_688_);
v___x_709_ = lean_box(0);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_709_);
v___x_711_ = v___x_702_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_dec_ref(v___x_696_);
lean_dec_ref(v_type_688_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___boxed(lean_object* v_u_714_, lean_object* v_type_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_714_, v_type_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(lean_object* v_u_722_, lean_object* v_type_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_722_, v_type_723_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___boxed(lean_object* v_u_736_, lean_object* v_type_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(v_u_736_, v_type_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec(v_a_738_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_s_752_){
_start:
{
lean_object* v_rings_753_; lean_object* v_typeIdOf_754_; lean_object* v_exprToRingId_755_; lean_object* v_semirings_756_; lean_object* v_stypeIdOf_757_; lean_object* v_exprToSemiringId_758_; lean_object* v_ncRings_759_; lean_object* v_exprToNCRingId_760_; lean_object* v_nctypeIdOf_761_; lean_object* v_ncSemirings_762_; lean_object* v_exprToNCSemiringId_763_; lean_object* v_ncstypeIdOf_764_; lean_object* v_steps_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_rings_753_ = lean_ctor_get(v_s_752_, 0);
v_typeIdOf_754_ = lean_ctor_get(v_s_752_, 1);
v_exprToRingId_755_ = lean_ctor_get(v_s_752_, 2);
v_semirings_756_ = lean_ctor_get(v_s_752_, 3);
v_stypeIdOf_757_ = lean_ctor_get(v_s_752_, 4);
v_exprToSemiringId_758_ = lean_ctor_get(v_s_752_, 5);
v_ncRings_759_ = lean_ctor_get(v_s_752_, 6);
v_exprToNCRingId_760_ = lean_ctor_get(v_s_752_, 7);
v_nctypeIdOf_761_ = lean_ctor_get(v_s_752_, 8);
v_ncSemirings_762_ = lean_ctor_get(v_s_752_, 9);
v_exprToNCSemiringId_763_ = lean_ctor_get(v_s_752_, 10);
v_ncstypeIdOf_764_ = lean_ctor_get(v_s_752_, 11);
v_steps_765_ = lean_ctor_get(v_s_752_, 12);
v___x_766_ = lean_array_get_size(v_semirings_756_);
v___x_767_ = lean_nat_dec_lt(v_a_750_, v___x_766_);
if (v___x_767_ == 0)
{
lean_dec(v_a_751_);
return v_s_752_;
}
else
{
lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_791_; 
lean_inc(v_steps_765_);
lean_inc_ref(v_ncstypeIdOf_764_);
lean_inc_ref(v_exprToNCSemiringId_763_);
lean_inc_ref(v_ncSemirings_762_);
lean_inc_ref(v_nctypeIdOf_761_);
lean_inc_ref(v_exprToNCRingId_760_);
lean_inc_ref(v_ncRings_759_);
lean_inc_ref(v_exprToSemiringId_758_);
lean_inc_ref(v_stypeIdOf_757_);
lean_inc_ref(v_semirings_756_);
lean_inc_ref(v_exprToRingId_755_);
lean_inc_ref(v_typeIdOf_754_);
lean_inc_ref(v_rings_753_);
v_isSharedCheck_791_ = !lean_is_exclusive(v_s_752_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; lean_object* v_unused_793_; lean_object* v_unused_794_; lean_object* v_unused_795_; lean_object* v_unused_796_; lean_object* v_unused_797_; lean_object* v_unused_798_; lean_object* v_unused_799_; lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; lean_object* v_unused_803_; lean_object* v_unused_804_; 
v_unused_792_ = lean_ctor_get(v_s_752_, 12);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v_s_752_, 11);
lean_dec(v_unused_793_);
v_unused_794_ = lean_ctor_get(v_s_752_, 10);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_s_752_, 9);
lean_dec(v_unused_795_);
v_unused_796_ = lean_ctor_get(v_s_752_, 8);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_s_752_, 7);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_s_752_, 6);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_s_752_, 5);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_s_752_, 4);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_s_752_, 3);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_s_752_, 2);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_s_752_, 1);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_s_752_, 0);
lean_dec(v_unused_804_);
v___x_769_ = v_s_752_;
v_isShared_770_ = v_isSharedCheck_791_;
goto v_resetjp_768_;
}
else
{
lean_dec(v_s_752_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_791_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_v_771_; lean_object* v_toSemiring_772_; lean_object* v_ringId_773_; lean_object* v_commSemiringInst_774_; lean_object* v_toQFn_x3f_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_789_; 
v_v_771_ = lean_array_fget(v_semirings_756_, v_a_750_);
v_toSemiring_772_ = lean_ctor_get(v_v_771_, 0);
v_ringId_773_ = lean_ctor_get(v_v_771_, 1);
v_commSemiringInst_774_ = lean_ctor_get(v_v_771_, 2);
v_toQFn_x3f_775_ = lean_ctor_get(v_v_771_, 4);
v_isSharedCheck_789_ = !lean_is_exclusive(v_v_771_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v_v_771_, 3);
lean_dec(v_unused_790_);
v___x_777_ = v_v_771_;
v_isShared_778_ = v_isSharedCheck_789_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_toQFn_x3f_775_);
lean_inc(v_commSemiringInst_774_);
lean_inc(v_ringId_773_);
lean_inc(v_toSemiring_772_);
lean_dec(v_v_771_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_789_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v_xs_x27_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_779_ = lean_box(0);
v_xs_x27_780_ = lean_array_fset(v_semirings_756_, v_a_750_, v___x_779_);
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v_a_751_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 3, v___x_781_);
v___x_783_ = v___x_777_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_toSemiring_772_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_ringId_773_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_commSemiringInst_774_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v_toQFn_x3f_775_);
v___x_783_ = v_reuseFailAlloc_788_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = lean_array_fset(v_xs_x27_780_, v_a_750_, v___x_783_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 3, v___x_784_);
v___x_786_ = v___x_769_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_rings_753_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_typeIdOf_754_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_exprToRingId_755_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_787_, 4, v_stypeIdOf_757_);
lean_ctor_set(v_reuseFailAlloc_787_, 5, v_exprToSemiringId_758_);
lean_ctor_set(v_reuseFailAlloc_787_, 6, v_ncRings_759_);
lean_ctor_set(v_reuseFailAlloc_787_, 7, v_exprToNCRingId_760_);
lean_ctor_set(v_reuseFailAlloc_787_, 8, v_nctypeIdOf_761_);
lean_ctor_set(v_reuseFailAlloc_787_, 9, v_ncSemirings_762_);
lean_ctor_set(v_reuseFailAlloc_787_, 10, v_exprToNCSemiringId_763_);
lean_ctor_set(v_reuseFailAlloc_787_, 11, v_ncstypeIdOf_764_);
lean_ctor_set(v_reuseFailAlloc_787_, 12, v_steps_765_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed(lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_s_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(v_a_805_, v_a_806_, v_s_807_);
lean_dec(v_a_805_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_855_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_855_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_855_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_855_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_addRightCancelInst_x3f_826_; 
v_addRightCancelInst_x3f_826_ = lean_ctor_get(v_a_822_, 3);
if (lean_obj_tag(v_addRightCancelInst_x3f_826_) == 1)
{
lean_object* v_val_827_; lean_object* v___x_829_; 
lean_inc_ref(v_addRightCancelInst_x3f_826_);
lean_dec(v_a_822_);
v_val_827_ = lean_ctor_get(v_addRightCancelInst_x3f_826_, 0);
lean_inc(v_val_827_);
lean_dec_ref(v_addRightCancelInst_x3f_826_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_val_827_);
v___x_829_ = v___x_824_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_val_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
else
{
lean_object* v_toSemiring_831_; lean_object* v_type_832_; lean_object* v_u_833_; lean_object* v___x_834_; 
lean_del_object(v___x_824_);
v_toSemiring_831_ = lean_ctor_get(v_a_822_, 0);
lean_inc_ref(v_toSemiring_831_);
lean_dec(v_a_822_);
v_type_832_ = lean_ctor_get(v_toSemiring_831_, 1);
lean_inc_ref(v_type_832_);
v_u_833_ = lean_ctor_get(v_toSemiring_831_, 2);
lean_inc(v_u_833_);
lean_dec_ref(v_toSemiring_831_);
v___x_834_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_833_, v_type_832_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___f_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref(v___x_834_);
lean_inc(v_a_835_);
lean_inc(v_a_809_);
v___f_836_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_836_, 0, v_a_809_);
lean_closure_set(v___f_836_, 1, v_a_835_);
v___x_837_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_838_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_837_, v___f_836_, v_a_810_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; 
v_unused_846_ = lean_ctor_get(v___x_838_, 0);
lean_dec(v_unused_846_);
v___x_840_ = v___x_838_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_dec(v___x_838_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v_a_835_);
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_835_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_a_835_);
v_a_847_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_838_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_838_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
else
{
return v___x_834_;
}
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
v_a_856_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_821_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_821_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___boxed(lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
lean_dec_ref(v_a_867_);
lean_dec(v_a_866_);
lean_dec(v_a_865_);
lean_dec(v_a_864_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_877_, lean_object* v_s_878_){
_start:
{
lean_object* v_id_879_; lean_object* v_type_880_; lean_object* v_u_881_; lean_object* v_semiringInst_882_; lean_object* v_mulFn_x3f_883_; lean_object* v_powFn_x3f_884_; lean_object* v_natCastFn_x3f_885_; lean_object* v_denote_886_; lean_object* v_vars_887_; lean_object* v_varMap_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_896_; 
v_id_879_ = lean_ctor_get(v_s_878_, 0);
v_type_880_ = lean_ctor_get(v_s_878_, 1);
v_u_881_ = lean_ctor_get(v_s_878_, 2);
v_semiringInst_882_ = lean_ctor_get(v_s_878_, 3);
v_mulFn_x3f_883_ = lean_ctor_get(v_s_878_, 5);
v_powFn_x3f_884_ = lean_ctor_get(v_s_878_, 6);
v_natCastFn_x3f_885_ = lean_ctor_get(v_s_878_, 7);
v_denote_886_ = lean_ctor_get(v_s_878_, 8);
v_vars_887_ = lean_ctor_get(v_s_878_, 9);
v_varMap_888_ = lean_ctor_get(v_s_878_, 10);
v_isSharedCheck_896_ = !lean_is_exclusive(v_s_878_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v_s_878_, 4);
lean_dec(v_unused_897_);
v___x_890_ = v_s_878_;
v_isShared_891_ = v_isSharedCheck_896_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_varMap_888_);
lean_inc(v_vars_887_);
lean_inc(v_denote_886_);
lean_inc(v_natCastFn_x3f_885_);
lean_inc(v_powFn_x3f_884_);
lean_inc(v_mulFn_x3f_883_);
lean_inc(v_semiringInst_882_);
lean_inc(v_u_881_);
lean_inc(v_type_880_);
lean_inc(v_id_879_);
lean_dec(v_s_878_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_896_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_892_, 0, v_addFn_877_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 4, v___x_892_);
v___x_894_ = v___x_890_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_id_879_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_type_880_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_u_881_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_semiringInst_882_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_895_, 5, v_mulFn_x3f_883_);
lean_ctor_set(v_reuseFailAlloc_895_, 6, v_powFn_x3f_884_);
lean_ctor_set(v_reuseFailAlloc_895_, 7, v_natCastFn_x3f_885_);
lean_ctor_set(v_reuseFailAlloc_895_, 8, v_denote_886_);
lean_ctor_set(v_reuseFailAlloc_895_, 9, v_vars_887_);
lean_ctor_set(v_reuseFailAlloc_895_, 10, v_varMap_888_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_898_, lean_object* v_addFn_899_, lean_object* v_____r_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = lean_apply_2(v_toPure_898_, lean_box(0), v_addFn_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_902_, lean_object* v_modifySemiring_903_, lean_object* v_toBind_904_, lean_object* v_addFn_905_){
_start:
{
lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
lean_inc_ref(v_addFn_905_);
v___f_906_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_906_, 0, v_addFn_905_);
v___f_907_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_907_, 0, v_toPure_902_);
lean_closure_set(v___f_907_, 1, v_addFn_905_);
v___x_908_ = lean_apply_1(v_modifySemiring_903_, v___f_906_);
v___x_909_ = lean_apply_4(v_toBind_904_, lean_box(0), lean_box(0), v___x_908_, v___f_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3(lean_object* v_toPure_927_, lean_object* v_inst_928_, lean_object* v_inst_929_, lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_toBind_932_, lean_object* v___f_933_, lean_object* v_s_934_){
_start:
{
lean_object* v_addFn_x3f_935_; 
v_addFn_x3f_935_ = lean_ctor_get(v_s_934_, 4);
if (lean_obj_tag(v_addFn_x3f_935_) == 1)
{
lean_object* v_val_936_; lean_object* v___x_937_; 
lean_inc_ref(v_addFn_x3f_935_);
lean_dec_ref(v_s_934_);
lean_dec(v___f_933_);
lean_dec(v_toBind_932_);
lean_dec_ref(v_inst_931_);
lean_dec_ref(v_inst_930_);
lean_dec_ref(v_inst_929_);
lean_dec(v_inst_928_);
v_val_936_ = lean_ctor_get(v_addFn_x3f_935_, 0);
lean_inc(v_val_936_);
lean_dec_ref(v_addFn_x3f_935_);
v___x_937_ = lean_apply_2(v_toPure_927_, lean_box(0), v_val_936_);
return v___x_937_;
}
else
{
lean_object* v_type_938_; lean_object* v_u_939_; lean_object* v_semiringInst_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_expectedInst_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v_toPure_927_);
v_type_938_ = lean_ctor_get(v_s_934_, 1);
lean_inc_ref(v_type_938_);
v_u_939_ = lean_ctor_get(v_s_934_, 2);
lean_inc(v_u_939_);
v_semiringInst_940_ = lean_ctor_get(v_s_934_, 3);
lean_inc_ref(v_semiringInst_940_);
lean_dec_ref(v_s_934_);
v___x_941_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_942_ = lean_box(0);
lean_inc(v_u_939_);
v___x_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_943_, 0, v_u_939_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
lean_inc_ref(v___x_943_);
v___x_944_ = l_Lean_mkConst(v___x_941_, v___x_943_);
v___x_945_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_946_ = l_Lean_mkConst(v___x_945_, v___x_943_);
lean_inc_ref(v_type_938_);
v___x_947_ = l_Lean_mkAppB(v___x_946_, v_type_938_, v_semiringInst_940_);
lean_inc_ref(v_type_938_);
v_expectedInst_948_ = l_Lean_mkAppB(v___x_944_, v_type_938_, v___x_947_);
v___x_949_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6));
v___x_950_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8));
v___x_951_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_928_, v_inst_929_, v_inst_930_, v_inst_931_, v_type_938_, v_u_939_, v___x_949_, v___x_950_, v_expectedInst_948_);
v___x_952_ = lean_apply_4(v_toBind_932_, lean_box(0), lean_box(0), v___x_951_, v___f_933_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(lean_object* v_inst_953_, lean_object* v_inst_954_, lean_object* v_inst_955_, lean_object* v_inst_956_, lean_object* v_inst_957_){
_start:
{
lean_object* v_toApplicative_958_; lean_object* v_toBind_959_; lean_object* v_getSemiring_960_; lean_object* v_modifySemiring_961_; lean_object* v_toPure_962_; lean_object* v___f_963_; lean_object* v___f_964_; lean_object* v___x_965_; 
v_toApplicative_958_ = lean_ctor_get(v_inst_955_, 0);
v_toBind_959_ = lean_ctor_get(v_inst_955_, 1);
lean_inc(v_toBind_959_);
v_getSemiring_960_ = lean_ctor_get(v_inst_957_, 0);
lean_inc(v_getSemiring_960_);
v_modifySemiring_961_ = lean_ctor_get(v_inst_957_, 1);
lean_inc(v_modifySemiring_961_);
lean_dec_ref(v_inst_957_);
v_toPure_962_ = lean_ctor_get(v_toApplicative_958_, 1);
lean_inc(v_toPure_962_);
lean_inc(v_toBind_959_);
lean_inc(v_toPure_962_);
v___f_963_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_963_, 0, v_toPure_962_);
lean_closure_set(v___f_963_, 1, v_modifySemiring_961_);
lean_closure_set(v___f_963_, 2, v_toBind_959_);
lean_inc(v_toBind_959_);
v___f_964_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_964_, 0, v_toPure_962_);
lean_closure_set(v___f_964_, 1, v_inst_953_);
lean_closure_set(v___f_964_, 2, v_inst_954_);
lean_closure_set(v___f_964_, 3, v_inst_955_);
lean_closure_set(v___f_964_, 4, v_inst_956_);
lean_closure_set(v___f_964_, 5, v_toBind_959_);
lean_closure_set(v___f_964_, 6, v___f_963_);
v___x_965_ = lean_apply_4(v_toBind_959_, lean_box(0), lean_box(0), v_getSemiring_960_, v___f_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27(lean_object* v_m_966_, lean_object* v_inst_967_, lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_inst_970_, lean_object* v_inst_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(v_inst_967_, v_inst_968_, v_inst_969_, v_inst_970_, v_inst_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_973_, lean_object* v_s_974_){
_start:
{
lean_object* v_id_975_; lean_object* v_type_976_; lean_object* v_u_977_; lean_object* v_semiringInst_978_; lean_object* v_addFn_x3f_979_; lean_object* v_powFn_x3f_980_; lean_object* v_natCastFn_x3f_981_; lean_object* v_denote_982_; lean_object* v_vars_983_; lean_object* v_varMap_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_992_; 
v_id_975_ = lean_ctor_get(v_s_974_, 0);
v_type_976_ = lean_ctor_get(v_s_974_, 1);
v_u_977_ = lean_ctor_get(v_s_974_, 2);
v_semiringInst_978_ = lean_ctor_get(v_s_974_, 3);
v_addFn_x3f_979_ = lean_ctor_get(v_s_974_, 4);
v_powFn_x3f_980_ = lean_ctor_get(v_s_974_, 6);
v_natCastFn_x3f_981_ = lean_ctor_get(v_s_974_, 7);
v_denote_982_ = lean_ctor_get(v_s_974_, 8);
v_vars_983_ = lean_ctor_get(v_s_974_, 9);
v_varMap_984_ = lean_ctor_get(v_s_974_, 10);
v_isSharedCheck_992_ = !lean_is_exclusive(v_s_974_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; 
v_unused_993_ = lean_ctor_get(v_s_974_, 5);
lean_dec(v_unused_993_);
v___x_986_ = v_s_974_;
v_isShared_987_ = v_isSharedCheck_992_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_varMap_984_);
lean_inc(v_vars_983_);
lean_inc(v_denote_982_);
lean_inc(v_natCastFn_x3f_981_);
lean_inc(v_powFn_x3f_980_);
lean_inc(v_addFn_x3f_979_);
lean_inc(v_semiringInst_978_);
lean_inc(v_u_977_);
lean_inc(v_type_976_);
lean_inc(v_id_975_);
lean_dec(v_s_974_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_992_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v_mulFn_973_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 5, v___x_988_);
v___x_990_ = v___x_986_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_id_975_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_type_976_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v_u_977_);
lean_ctor_set(v_reuseFailAlloc_991_, 3, v_semiringInst_978_);
lean_ctor_set(v_reuseFailAlloc_991_, 4, v_addFn_x3f_979_);
lean_ctor_set(v_reuseFailAlloc_991_, 5, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_991_, 6, v_powFn_x3f_980_);
lean_ctor_set(v_reuseFailAlloc_991_, 7, v_natCastFn_x3f_981_);
lean_ctor_set(v_reuseFailAlloc_991_, 8, v_denote_982_);
lean_ctor_set(v_reuseFailAlloc_991_, 9, v_vars_983_);
lean_ctor_set(v_reuseFailAlloc_991_, 10, v_varMap_984_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_994_, lean_object* v_mulFn_995_, lean_object* v_____r_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = lean_apply_2(v_toPure_994_, lean_box(0), v_mulFn_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_998_, lean_object* v_modifySemiring_999_, lean_object* v_toBind_1000_, lean_object* v_mulFn_1001_){
_start:
{
lean_object* v___f_1002_; lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_inc_ref(v_mulFn_1001_);
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1002_, 0, v_mulFn_1001_);
v___f_1003_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1003_, 0, v_toPure_998_);
lean_closure_set(v___f_1003_, 1, v_mulFn_1001_);
v___x_1004_ = lean_apply_1(v_modifySemiring_999_, v___f_1002_);
v___x_1005_ = lean_apply_4(v_toBind_1000_, lean_box(0), lean_box(0), v___x_1004_, v___f_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3(lean_object* v_toPure_1022_, lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_toBind_1027_, lean_object* v___f_1028_, lean_object* v_s_1029_){
_start:
{
lean_object* v_mulFn_x3f_1030_; 
v_mulFn_x3f_1030_ = lean_ctor_get(v_s_1029_, 5);
if (lean_obj_tag(v_mulFn_x3f_1030_) == 1)
{
lean_object* v_val_1031_; lean_object* v___x_1032_; 
lean_inc_ref(v_mulFn_x3f_1030_);
lean_dec_ref(v_s_1029_);
lean_dec(v___f_1028_);
lean_dec(v_toBind_1027_);
lean_dec_ref(v_inst_1026_);
lean_dec_ref(v_inst_1025_);
lean_dec_ref(v_inst_1024_);
lean_dec(v_inst_1023_);
v_val_1031_ = lean_ctor_get(v_mulFn_x3f_1030_, 0);
lean_inc(v_val_1031_);
lean_dec_ref(v_mulFn_x3f_1030_);
v___x_1032_ = lean_apply_2(v_toPure_1022_, lean_box(0), v_val_1031_);
return v___x_1032_;
}
else
{
lean_object* v_type_1033_; lean_object* v_u_1034_; lean_object* v_semiringInst_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v_expectedInst_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec(v_toPure_1022_);
v_type_1033_ = lean_ctor_get(v_s_1029_, 1);
lean_inc_ref(v_type_1033_);
v_u_1034_ = lean_ctor_get(v_s_1029_, 2);
lean_inc(v_u_1034_);
v_semiringInst_1035_ = lean_ctor_get(v_s_1029_, 3);
lean_inc_ref(v_semiringInst_1035_);
lean_dec_ref(v_s_1029_);
v___x_1036_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_1037_ = lean_box(0);
lean_inc(v_u_1034_);
v___x_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1038_, 0, v_u_1034_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
lean_inc_ref(v___x_1038_);
v___x_1039_ = l_Lean_mkConst(v___x_1036_, v___x_1038_);
v___x_1040_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_1041_ = l_Lean_mkConst(v___x_1040_, v___x_1038_);
lean_inc_ref(v_type_1033_);
v___x_1042_ = l_Lean_mkAppB(v___x_1041_, v_type_1033_, v_semiringInst_1035_);
lean_inc_ref(v_type_1033_);
v_expectedInst_1043_ = l_Lean_mkAppB(v___x_1039_, v_type_1033_, v___x_1042_);
v___x_1044_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5));
v___x_1045_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7));
v___x_1046_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_1023_, v_inst_1024_, v_inst_1025_, v_inst_1026_, v_type_1033_, v_u_1034_, v___x_1044_, v___x_1045_, v_expectedInst_1043_);
v___x_1047_ = lean_apply_4(v_toBind_1027_, lean_box(0), lean_box(0), v___x_1046_, v___f_1028_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(lean_object* v_inst_1048_, lean_object* v_inst_1049_, lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_){
_start:
{
lean_object* v_toApplicative_1053_; lean_object* v_toBind_1054_; lean_object* v_getSemiring_1055_; lean_object* v_modifySemiring_1056_; lean_object* v_toPure_1057_; lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; 
v_toApplicative_1053_ = lean_ctor_get(v_inst_1050_, 0);
v_toBind_1054_ = lean_ctor_get(v_inst_1050_, 1);
lean_inc(v_toBind_1054_);
v_getSemiring_1055_ = lean_ctor_get(v_inst_1052_, 0);
lean_inc(v_getSemiring_1055_);
v_modifySemiring_1056_ = lean_ctor_get(v_inst_1052_, 1);
lean_inc(v_modifySemiring_1056_);
lean_dec_ref(v_inst_1052_);
v_toPure_1057_ = lean_ctor_get(v_toApplicative_1053_, 1);
lean_inc(v_toPure_1057_);
lean_inc(v_toBind_1054_);
lean_inc(v_toPure_1057_);
v___f_1058_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1058_, 0, v_toPure_1057_);
lean_closure_set(v___f_1058_, 1, v_modifySemiring_1056_);
lean_closure_set(v___f_1058_, 2, v_toBind_1054_);
lean_inc(v_toBind_1054_);
v___f_1059_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1059_, 0, v_toPure_1057_);
lean_closure_set(v___f_1059_, 1, v_inst_1048_);
lean_closure_set(v___f_1059_, 2, v_inst_1049_);
lean_closure_set(v___f_1059_, 3, v_inst_1050_);
lean_closure_set(v___f_1059_, 4, v_inst_1051_);
lean_closure_set(v___f_1059_, 5, v_toBind_1054_);
lean_closure_set(v___f_1059_, 6, v___f_1058_);
v___x_1060_ = lean_apply_4(v_toBind_1054_, lean_box(0), lean_box(0), v_getSemiring_1055_, v___f_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27(lean_object* v_m_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(v_inst_1062_, v_inst_1063_, v_inst_1064_, v_inst_1065_, v_inst_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_1068_, lean_object* v_s_1069_){
_start:
{
lean_object* v_id_1070_; lean_object* v_type_1071_; lean_object* v_u_1072_; lean_object* v_semiringInst_1073_; lean_object* v_addFn_x3f_1074_; lean_object* v_mulFn_x3f_1075_; lean_object* v_natCastFn_x3f_1076_; lean_object* v_denote_1077_; lean_object* v_vars_1078_; lean_object* v_varMap_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1087_; 
v_id_1070_ = lean_ctor_get(v_s_1069_, 0);
v_type_1071_ = lean_ctor_get(v_s_1069_, 1);
v_u_1072_ = lean_ctor_get(v_s_1069_, 2);
v_semiringInst_1073_ = lean_ctor_get(v_s_1069_, 3);
v_addFn_x3f_1074_ = lean_ctor_get(v_s_1069_, 4);
v_mulFn_x3f_1075_ = lean_ctor_get(v_s_1069_, 5);
v_natCastFn_x3f_1076_ = lean_ctor_get(v_s_1069_, 7);
v_denote_1077_ = lean_ctor_get(v_s_1069_, 8);
v_vars_1078_ = lean_ctor_get(v_s_1069_, 9);
v_varMap_1079_ = lean_ctor_get(v_s_1069_, 10);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_s_1069_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v_s_1069_, 6);
lean_dec(v_unused_1088_);
v___x_1081_ = v_s_1069_;
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_varMap_1079_);
lean_inc(v_vars_1078_);
lean_inc(v_denote_1077_);
lean_inc(v_natCastFn_x3f_1076_);
lean_inc(v_mulFn_x3f_1075_);
lean_inc(v_addFn_x3f_1074_);
lean_inc(v_semiringInst_1073_);
lean_inc(v_u_1072_);
lean_inc(v_type_1071_);
lean_inc(v_id_1070_);
lean_dec(v_s_1069_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v_powFn_1068_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 6, v___x_1083_);
v___x_1085_ = v___x_1081_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_id_1070_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_type_1071_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_u_1072_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v_semiringInst_1073_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v_addFn_x3f_1074_);
lean_ctor_set(v_reuseFailAlloc_1086_, 5, v_mulFn_x3f_1075_);
lean_ctor_set(v_reuseFailAlloc_1086_, 6, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1086_, 7, v_natCastFn_x3f_1076_);
lean_ctor_set(v_reuseFailAlloc_1086_, 8, v_denote_1077_);
lean_ctor_set(v_reuseFailAlloc_1086_, 9, v_vars_1078_);
lean_ctor_set(v_reuseFailAlloc_1086_, 10, v_varMap_1079_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_1089_, lean_object* v_powFn_1090_, lean_object* v_____r_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_apply_2(v_toPure_1089_, lean_box(0), v_powFn_1090_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_1093_, lean_object* v_modifySemiring_1094_, lean_object* v_toBind_1095_, lean_object* v_powFn_1096_){
_start:
{
lean_object* v___f_1097_; lean_object* v___f_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_inc_ref(v_powFn_1096_);
v___f_1097_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1097_, 0, v_powFn_1096_);
v___f_1098_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1098_, 0, v_toPure_1093_);
lean_closure_set(v___f_1098_, 1, v_powFn_1096_);
v___x_1099_ = lean_apply_1(v_modifySemiring_1094_, v___f_1097_);
v___x_1100_ = lean_apply_4(v_toBind_1095_, lean_box(0), lean_box(0), v___x_1099_, v___f_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3(lean_object* v_toPure_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_toBind_1106_, lean_object* v___f_1107_, lean_object* v_s_1108_){
_start:
{
lean_object* v_powFn_x3f_1109_; 
v_powFn_x3f_1109_ = lean_ctor_get(v_s_1108_, 6);
if (lean_obj_tag(v_powFn_x3f_1109_) == 1)
{
lean_object* v_val_1110_; lean_object* v___x_1111_; 
lean_inc_ref(v_powFn_x3f_1109_);
lean_dec_ref(v_s_1108_);
lean_dec(v___f_1107_);
lean_dec(v_toBind_1106_);
lean_dec_ref(v_inst_1105_);
lean_dec_ref(v_inst_1104_);
lean_dec_ref(v_inst_1103_);
lean_dec(v_inst_1102_);
v_val_1110_ = lean_ctor_get(v_powFn_x3f_1109_, 0);
lean_inc(v_val_1110_);
lean_dec_ref(v_powFn_x3f_1109_);
v___x_1111_ = lean_apply_2(v_toPure_1101_, lean_box(0), v_val_1110_);
return v___x_1111_;
}
else
{
lean_object* v_type_1112_; lean_object* v_u_1113_; lean_object* v_semiringInst_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v_toPure_1101_);
v_type_1112_ = lean_ctor_get(v_s_1108_, 1);
lean_inc_ref(v_type_1112_);
v_u_1113_ = lean_ctor_get(v_s_1108_, 2);
lean_inc(v_u_1113_);
v_semiringInst_1114_ = lean_ctor_get(v_s_1108_, 3);
lean_inc_ref(v_semiringInst_1114_);
lean_dec_ref(v_s_1108_);
v___x_1115_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(v_inst_1102_, v_inst_1103_, v_inst_1104_, v_inst_1105_, v_u_1113_, v_type_1112_, v_semiringInst_1114_);
v___x_1116_ = lean_apply_4(v_toBind_1106_, lean_box(0), lean_box(0), v___x_1115_, v___f_1107_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_){
_start:
{
lean_object* v_toApplicative_1122_; lean_object* v_toBind_1123_; lean_object* v_getSemiring_1124_; lean_object* v_modifySemiring_1125_; lean_object* v_toPure_1126_; lean_object* v___f_1127_; lean_object* v___f_1128_; lean_object* v___x_1129_; 
v_toApplicative_1122_ = lean_ctor_get(v_inst_1119_, 0);
v_toBind_1123_ = lean_ctor_get(v_inst_1119_, 1);
lean_inc(v_toBind_1123_);
v_getSemiring_1124_ = lean_ctor_get(v_inst_1121_, 0);
lean_inc(v_getSemiring_1124_);
v_modifySemiring_1125_ = lean_ctor_get(v_inst_1121_, 1);
lean_inc(v_modifySemiring_1125_);
lean_dec_ref(v_inst_1121_);
v_toPure_1126_ = lean_ctor_get(v_toApplicative_1122_, 1);
lean_inc(v_toPure_1126_);
lean_inc(v_toBind_1123_);
lean_inc(v_toPure_1126_);
v___f_1127_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1127_, 0, v_toPure_1126_);
lean_closure_set(v___f_1127_, 1, v_modifySemiring_1125_);
lean_closure_set(v___f_1127_, 2, v_toBind_1123_);
lean_inc(v_toBind_1123_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1128_, 0, v_toPure_1126_);
lean_closure_set(v___f_1128_, 1, v_inst_1117_);
lean_closure_set(v___f_1128_, 2, v_inst_1118_);
lean_closure_set(v___f_1128_, 3, v_inst_1119_);
lean_closure_set(v___f_1128_, 4, v_inst_1120_);
lean_closure_set(v___f_1128_, 5, v_toBind_1123_);
lean_closure_set(v___f_1128_, 6, v___f_1127_);
v___x_1129_ = lean_apply_4(v_toBind_1123_, lean_box(0), lean_box(0), v_getSemiring_1124_, v___f_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27(lean_object* v_m_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(v_inst_1131_, v_inst_1132_, v_inst_1133_, v_inst_1134_, v_inst_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_1137_, lean_object* v_s_1138_){
_start:
{
lean_object* v_id_1139_; lean_object* v_type_1140_; lean_object* v_u_1141_; lean_object* v_semiringInst_1142_; lean_object* v_addFn_x3f_1143_; lean_object* v_mulFn_x3f_1144_; lean_object* v_powFn_x3f_1145_; lean_object* v_denote_1146_; lean_object* v_vars_1147_; lean_object* v_varMap_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1156_; 
v_id_1139_ = lean_ctor_get(v_s_1138_, 0);
v_type_1140_ = lean_ctor_get(v_s_1138_, 1);
v_u_1141_ = lean_ctor_get(v_s_1138_, 2);
v_semiringInst_1142_ = lean_ctor_get(v_s_1138_, 3);
v_addFn_x3f_1143_ = lean_ctor_get(v_s_1138_, 4);
v_mulFn_x3f_1144_ = lean_ctor_get(v_s_1138_, 5);
v_powFn_x3f_1145_ = lean_ctor_get(v_s_1138_, 6);
v_denote_1146_ = lean_ctor_get(v_s_1138_, 8);
v_vars_1147_ = lean_ctor_get(v_s_1138_, 9);
v_varMap_1148_ = lean_ctor_get(v_s_1138_, 10);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_s_1138_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; 
v_unused_1157_ = lean_ctor_get(v_s_1138_, 7);
lean_dec(v_unused_1157_);
v___x_1150_ = v_s_1138_;
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_varMap_1148_);
lean_inc(v_vars_1147_);
lean_inc(v_denote_1146_);
lean_inc(v_powFn_x3f_1145_);
lean_inc(v_mulFn_x3f_1144_);
lean_inc(v_addFn_x3f_1143_);
lean_inc(v_semiringInst_1142_);
lean_inc(v_u_1141_);
lean_inc(v_type_1140_);
lean_inc(v_id_1139_);
lean_dec(v_s_1138_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_natCastFn_1137_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 7, v___x_1152_);
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_id_1139_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_type_1140_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_u_1141_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v_semiringInst_1142_);
lean_ctor_set(v_reuseFailAlloc_1155_, 4, v_addFn_x3f_1143_);
lean_ctor_set(v_reuseFailAlloc_1155_, 5, v_mulFn_x3f_1144_);
lean_ctor_set(v_reuseFailAlloc_1155_, 6, v_powFn_x3f_1145_);
lean_ctor_set(v_reuseFailAlloc_1155_, 7, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1155_, 8, v_denote_1146_);
lean_ctor_set(v_reuseFailAlloc_1155_, 9, v_vars_1147_);
lean_ctor_set(v_reuseFailAlloc_1155_, 10, v_varMap_1148_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_1158_, lean_object* v_natCastFn_1159_, lean_object* v_____r_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_apply_2(v_toPure_1158_, lean_box(0), v_natCastFn_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_1162_, lean_object* v_modifySemiring_1163_, lean_object* v_toBind_1164_, lean_object* v_natCastFn_1165_){
_start:
{
lean_object* v___f_1166_; lean_object* v___f_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_inc_ref(v_natCastFn_1165_);
v___f_1166_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1166_, 0, v_natCastFn_1165_);
v___f_1167_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1167_, 0, v_toPure_1162_);
lean_closure_set(v___f_1167_, 1, v_natCastFn_1165_);
v___x_1168_ = lean_apply_1(v_modifySemiring_1163_, v___f_1166_);
v___x_1169_ = lean_apply_4(v_toBind_1164_, lean_box(0), lean_box(0), v___x_1168_, v___f_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3(lean_object* v_toPure_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_toBind_1174_, lean_object* v___f_1175_, lean_object* v_s_1176_){
_start:
{
lean_object* v_natCastFn_x3f_1177_; 
v_natCastFn_x3f_1177_ = lean_ctor_get(v_s_1176_, 7);
if (lean_obj_tag(v_natCastFn_x3f_1177_) == 1)
{
lean_object* v_val_1178_; lean_object* v___x_1179_; 
lean_inc_ref(v_natCastFn_x3f_1177_);
lean_dec_ref(v_s_1176_);
lean_dec(v___f_1175_);
lean_dec(v_toBind_1174_);
lean_dec_ref(v_inst_1173_);
lean_dec_ref(v_inst_1172_);
lean_dec(v_inst_1171_);
v_val_1178_ = lean_ctor_get(v_natCastFn_x3f_1177_, 0);
lean_inc(v_val_1178_);
lean_dec_ref(v_natCastFn_x3f_1177_);
v___x_1179_ = lean_apply_2(v_toPure_1170_, lean_box(0), v_val_1178_);
return v___x_1179_;
}
else
{
lean_object* v_type_1180_; lean_object* v_u_1181_; lean_object* v_semiringInst_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec(v_toPure_1170_);
v_type_1180_ = lean_ctor_get(v_s_1176_, 1);
lean_inc_ref(v_type_1180_);
v_u_1181_ = lean_ctor_get(v_s_1176_, 2);
lean_inc(v_u_1181_);
v_semiringInst_1182_ = lean_ctor_get(v_s_1176_, 3);
lean_inc_ref(v_semiringInst_1182_);
lean_dec_ref(v_s_1176_);
v___x_1183_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(v_inst_1171_, v_inst_1172_, v_inst_1173_, v_u_1181_, v_type_1180_, v_semiringInst_1182_);
v___x_1184_ = lean_apply_4(v_toBind_1174_, lean_box(0), lean_box(0), v___x_1183_, v___f_1175_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_){
_start:
{
lean_object* v_toApplicative_1189_; lean_object* v_toBind_1190_; lean_object* v_getSemiring_1191_; lean_object* v_modifySemiring_1192_; lean_object* v_toPure_1193_; lean_object* v___f_1194_; lean_object* v___f_1195_; lean_object* v___x_1196_; 
v_toApplicative_1189_ = lean_ctor_get(v_inst_1186_, 0);
v_toBind_1190_ = lean_ctor_get(v_inst_1186_, 1);
lean_inc(v_toBind_1190_);
v_getSemiring_1191_ = lean_ctor_get(v_inst_1188_, 0);
lean_inc(v_getSemiring_1191_);
v_modifySemiring_1192_ = lean_ctor_get(v_inst_1188_, 1);
lean_inc(v_modifySemiring_1192_);
lean_dec_ref(v_inst_1188_);
v_toPure_1193_ = lean_ctor_get(v_toApplicative_1189_, 1);
lean_inc(v_toPure_1193_);
lean_inc(v_toBind_1190_);
lean_inc(v_toPure_1193_);
v___f_1194_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1194_, 0, v_toPure_1193_);
lean_closure_set(v___f_1194_, 1, v_modifySemiring_1192_);
lean_closure_set(v___f_1194_, 2, v_toBind_1190_);
lean_inc(v_toBind_1190_);
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1195_, 0, v_toPure_1193_);
lean_closure_set(v___f_1195_, 1, v_inst_1185_);
lean_closure_set(v___f_1195_, 2, v_inst_1186_);
lean_closure_set(v___f_1195_, 3, v_inst_1187_);
lean_closure_set(v___f_1195_, 4, v_toBind_1190_);
lean_closure_set(v___f_1195_, 5, v___f_1194_);
v___x_1196_ = lean_apply_4(v_toBind_1190_, lean_box(0), lean_box(0), v_getSemiring_1191_, v___f_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27(lean_object* v_m_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(v_inst_1198_, v_inst_1199_, v_inst_1200_, v_inst_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1203_, lean_object* v_vals_1204_, lean_object* v_i_1205_, lean_object* v_k_1206_){
_start:
{
lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = lean_array_get_size(v_keys_1203_);
v___x_1208_ = lean_nat_dec_lt(v_i_1205_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; 
lean_dec(v_i_1205_);
v___x_1209_ = lean_box(0);
return v___x_1209_;
}
else
{
lean_object* v_k_x27_1210_; uint8_t v___x_1211_; 
v_k_x27_1210_ = lean_array_fget_borrowed(v_keys_1203_, v_i_1205_);
v___x_1211_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_1206_, v_k_x27_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_nat_add(v_i_1205_, v___x_1212_);
lean_dec(v_i_1205_);
v_i_1205_ = v___x_1213_;
goto _start;
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_array_fget_borrowed(v_vals_1204_, v_i_1205_);
lean_dec(v_i_1205_);
lean_inc(v___x_1215_);
v___x_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1217_, lean_object* v_vals_1218_, lean_object* v_i_1219_, lean_object* v_k_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1217_, v_vals_1218_, v_i_1219_, v_k_1220_);
lean_dec_ref(v_k_1220_);
lean_dec_ref(v_vals_1218_);
lean_dec_ref(v_keys_1217_);
return v_res_1221_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1222_; size_t v___x_1223_; size_t v___x_1224_; 
v___x_1222_ = ((size_t)5ULL);
v___x_1223_ = ((size_t)1ULL);
v___x_1224_ = lean_usize_shift_left(v___x_1223_, v___x_1222_);
return v___x_1224_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1225_; size_t v___x_1226_; size_t v___x_1227_; 
v___x_1225_ = ((size_t)1ULL);
v___x_1226_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0);
v___x_1227_ = lean_usize_sub(v___x_1226_, v___x_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_1228_, size_t v_x_1229_, lean_object* v_x_1230_){
_start:
{
if (lean_obj_tag(v_x_1228_) == 0)
{
lean_object* v_es_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1252_; 
v_es_1231_ = lean_ctor_get(v_x_1228_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_x_1228_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1233_ = v_x_1228_;
v_isShared_1234_ = v_isSharedCheck_1252_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_es_1231_);
lean_dec(v_x_1228_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1252_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; size_t v___x_1238_; lean_object* v_j_1239_; lean_object* v___x_1240_; 
v___x_1235_ = lean_box(2);
v___x_1236_ = ((size_t)5ULL);
v___x_1237_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1238_ = lean_usize_land(v_x_1229_, v___x_1237_);
v_j_1239_ = lean_usize_to_nat(v___x_1238_);
v___x_1240_ = lean_array_get(v___x_1235_, v_es_1231_, v_j_1239_);
lean_dec(v_j_1239_);
lean_dec_ref(v_es_1231_);
switch(lean_obj_tag(v___x_1240_))
{
case 0:
{
lean_object* v_key_1241_; lean_object* v_val_1242_; uint8_t v___x_1243_; 
v_key_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_key_1241_);
v_val_1242_ = lean_ctor_get(v___x_1240_, 1);
lean_inc(v_val_1242_);
lean_dec_ref(v___x_1240_);
v___x_1243_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1230_, v_key_1241_);
lean_dec(v_key_1241_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
lean_dec(v_val_1242_);
lean_del_object(v___x_1233_);
v___x_1244_ = lean_box(0);
return v___x_1244_;
}
else
{
lean_object* v___x_1246_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set_tag(v___x_1233_, 1);
lean_ctor_set(v___x_1233_, 0, v_val_1242_);
v___x_1246_ = v___x_1233_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_val_1242_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
case 1:
{
lean_object* v_node_1248_; size_t v___x_1249_; 
lean_del_object(v___x_1233_);
v_node_1248_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_node_1248_);
lean_dec_ref(v___x_1240_);
v___x_1249_ = lean_usize_shift_right(v_x_1229_, v___x_1236_);
v_x_1228_ = v_node_1248_;
v_x_1229_ = v___x_1249_;
goto _start;
}
default: 
{
lean_object* v___x_1251_; 
lean_del_object(v___x_1233_);
v___x_1251_ = lean_box(0);
return v___x_1251_;
}
}
}
}
else
{
lean_object* v_ks_1253_; lean_object* v_vs_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_ks_1253_ = lean_ctor_get(v_x_1228_, 0);
lean_inc_ref(v_ks_1253_);
v_vs_1254_ = lean_ctor_get(v_x_1228_, 1);
lean_inc_ref(v_vs_1254_);
lean_dec_ref(v_x_1228_);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1253_, v_vs_1254_, v___x_1255_, v_x_1230_);
lean_dec_ref(v_vs_1254_);
lean_dec_ref(v_ks_1253_);
return v___x_1256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
size_t v_x_867__boxed_1260_; lean_object* v_res_1261_; 
v_x_867__boxed_1260_ = lean_unbox_usize(v_x_1258_);
lean_dec(v_x_1258_);
v_res_1261_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1257_, v_x_867__boxed_1260_, v_x_1259_);
lean_dec_ref(v_x_1259_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
uint64_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1263_);
v___x_1265_ = lean_uint64_to_usize(v___x_1264_);
v___x_1266_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1262_, v___x_1265_, v_x_1263_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_1267_, v_x_1268_);
lean_dec_ref(v_x_1268_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(lean_object* v_e_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1284_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1284_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1284_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_exprToSemiringId_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v_exprToSemiringId_1279_ = lean_ctor_get(v_a_1275_, 5);
lean_inc_ref(v_exprToSemiringId_1279_);
lean_dec(v_a_1275_);
v___x_1280_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_exprToSemiringId_1279_, v_e_1270_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1280_);
v___x_1282_ = v___x_1277_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_a_1285_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1274_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1274_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg___boxed(lean_object* v_e_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1293_, v_a_1294_, v_a_1295_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_e_1293_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(lean_object* v_e_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1298_, v_a_1299_, v_a_1307_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(lean_object* v_e_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(v_e_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_e_1311_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(lean_object* v_00_u03b2_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_1325_, v_x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(v_00_u03b2_1328_, v_x_1329_, v_x_1330_);
lean_dec_ref(v_x_1330_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1332_, lean_object* v_x_1333_, size_t v_x_1334_, lean_object* v_x_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1333_, v_x_1334_, v_x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1337_, lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
size_t v_x_996__boxed_1341_; lean_object* v_res_1342_; 
v_x_996__boxed_1341_ = lean_unbox_usize(v_x_1339_);
lean_dec(v_x_1339_);
v_res_1342_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(v_00_u03b2_1337_, v_x_1338_, v_x_996__boxed_1341_, v_x_1340_);
lean_dec_ref(v_x_1340_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1343_, lean_object* v_keys_1344_, lean_object* v_vals_1345_, lean_object* v_heq_1346_, lean_object* v_i_1347_, lean_object* v_k_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1344_, v_vals_1345_, v_i_1347_, v_k_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1350_, lean_object* v_keys_1351_, lean_object* v_vals_1352_, lean_object* v_heq_1353_, lean_object* v_i_1354_, lean_object* v_k_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1350_, v_keys_1351_, v_vals_1352_, v_heq_1353_, v_i_1354_, v_k_1355_);
lean_dec_ref(v_k_1355_);
lean_dec_ref(v_vals_1352_);
lean_dec_ref(v_keys_1351_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1357_, lean_object* v_x_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_){
_start:
{
lean_object* v_ks_1361_; lean_object* v_vs_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1386_; 
v_ks_1361_ = lean_ctor_get(v_x_1357_, 0);
v_vs_1362_ = lean_ctor_get(v_x_1357_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_x_1357_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1364_ = v_x_1357_;
v_isShared_1365_ = v_isSharedCheck_1386_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_vs_1362_);
lean_inc(v_ks_1361_);
lean_dec(v_x_1357_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1386_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = lean_array_get_size(v_ks_1361_);
v___x_1367_ = lean_nat_dec_lt(v_x_1358_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
lean_dec(v_x_1358_);
v___x_1368_ = lean_array_push(v_ks_1361_, v_x_1359_);
v___x_1369_ = lean_array_push(v_vs_1362_, v_x_1360_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v___x_1369_);
lean_ctor_set(v___x_1364_, 0, v___x_1368_);
v___x_1371_ = v___x_1364_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
else
{
lean_object* v_k_x27_1373_; uint8_t v___x_1374_; 
v_k_x27_1373_ = lean_array_fget_borrowed(v_ks_1361_, v_x_1358_);
v___x_1374_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1359_, v_k_x27_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1376_; 
if (v_isShared_1365_ == 0)
{
v___x_1376_ = v___x_1364_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_ks_1361_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_vs_1362_);
v___x_1376_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_unsigned_to_nat(1u);
v___x_1378_ = lean_nat_add(v_x_1358_, v___x_1377_);
lean_dec(v_x_1358_);
v_x_1357_ = v___x_1376_;
v_x_1358_ = v___x_1378_;
goto _start;
}
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1381_ = lean_array_fset(v_ks_1361_, v_x_1358_, v_x_1359_);
v___x_1382_ = lean_array_fset(v_vs_1362_, v_x_1358_, v_x_1360_);
lean_dec(v_x_1358_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v___x_1382_);
lean_ctor_set(v___x_1364_, 0, v___x_1381_);
v___x_1384_ = v___x_1364_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1387_, lean_object* v_k_1388_, lean_object* v_v_1389_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1387_, v___x_1390_, v_k_1388_, v_v_1389_);
return v___x_1391_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(lean_object* v_x_1393_, size_t v_x_1394_, size_t v_x_1395_, lean_object* v_x_1396_, lean_object* v_x_1397_){
_start:
{
if (lean_obj_tag(v_x_1393_) == 0)
{
lean_object* v_es_1398_; size_t v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; lean_object* v_j_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_es_1398_ = lean_ctor_get(v_x_1393_, 0);
v___x_1399_ = ((size_t)5ULL);
v___x_1400_ = ((size_t)1ULL);
v___x_1401_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1402_ = lean_usize_land(v_x_1394_, v___x_1401_);
v_j_1403_ = lean_usize_to_nat(v___x_1402_);
v___x_1404_ = lean_array_get_size(v_es_1398_);
v___x_1405_ = lean_nat_dec_lt(v_j_1403_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_dec(v_j_1403_);
lean_dec(v_x_1397_);
lean_dec_ref(v_x_1396_);
return v_x_1393_;
}
else
{
lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1442_; 
lean_inc_ref(v_es_1398_);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_x_1393_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; 
v_unused_1443_ = lean_ctor_get(v_x_1393_, 0);
lean_dec(v_unused_1443_);
v___x_1407_ = v_x_1393_;
v_isShared_1408_ = v_isSharedCheck_1442_;
goto v_resetjp_1406_;
}
else
{
lean_dec(v_x_1393_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1442_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v_v_1409_; lean_object* v___x_1410_; lean_object* v_xs_x27_1411_; lean_object* v___y_1413_; 
v_v_1409_ = lean_array_fget(v_es_1398_, v_j_1403_);
v___x_1410_ = lean_box(0);
v_xs_x27_1411_ = lean_array_fset(v_es_1398_, v_j_1403_, v___x_1410_);
switch(lean_obj_tag(v_v_1409_))
{
case 0:
{
lean_object* v_key_1418_; lean_object* v_val_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1429_; 
v_key_1418_ = lean_ctor_get(v_v_1409_, 0);
v_val_1419_ = lean_ctor_get(v_v_1409_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_v_1409_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1421_ = v_v_1409_;
v_isShared_1422_ = v_isSharedCheck_1429_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_val_1419_);
lean_inc(v_key_1418_);
lean_dec(v_v_1409_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1429_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
uint8_t v___x_1423_; 
v___x_1423_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1396_, v_key_1418_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_del_object(v___x_1421_);
v___x_1424_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1418_, v_val_1419_, v_x_1396_, v_x_1397_);
v___x_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
v___y_1413_ = v___x_1425_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1427_; 
lean_dec(v_val_1419_);
lean_dec(v_key_1418_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 1, v_x_1397_);
lean_ctor_set(v___x_1421_, 0, v_x_1396_);
v___x_1427_ = v___x_1421_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_x_1396_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_x_1397_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
v___y_1413_ = v___x_1427_;
goto v___jp_1412_;
}
}
}
}
case 1:
{
lean_object* v_node_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1440_; 
v_node_1430_ = lean_ctor_get(v_v_1409_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_v_1409_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1432_ = v_v_1409_;
v_isShared_1433_ = v_isSharedCheck_1440_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_node_1430_);
lean_dec(v_v_1409_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1440_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
size_t v___x_1434_; size_t v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1434_ = lean_usize_shift_right(v_x_1394_, v___x_1399_);
v___x_1435_ = lean_usize_add(v_x_1395_, v___x_1400_);
v___x_1436_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_node_1430_, v___x_1434_, v___x_1435_, v_x_1396_, v_x_1397_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1436_);
v___x_1438_ = v___x_1432_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
v___y_1413_ = v___x_1438_;
goto v___jp_1412_;
}
}
}
default: 
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v_x_1396_);
lean_ctor_set(v___x_1441_, 1, v_x_1397_);
v___y_1413_ = v___x_1441_;
goto v___jp_1412_;
}
}
v___jp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = lean_array_fset(v_xs_x27_1411_, v_j_1403_, v___y_1413_);
lean_dec(v_j_1403_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1414_);
v___x_1416_ = v___x_1407_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
else
{
lean_object* v_ks_1444_; lean_object* v_vs_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1465_; 
v_ks_1444_ = lean_ctor_get(v_x_1393_, 0);
v_vs_1445_ = lean_ctor_get(v_x_1393_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_x_1393_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1447_ = v_x_1393_;
v_isShared_1448_ = v_isSharedCheck_1465_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_vs_1445_);
lean_inc(v_ks_1444_);
lean_dec(v_x_1393_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1465_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_ks_1444_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_vs_1445_);
v___x_1450_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v_newNode_1451_; uint8_t v___y_1453_; size_t v___x_1459_; uint8_t v___x_1460_; 
v_newNode_1451_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v___x_1450_, v_x_1396_, v_x_1397_);
v___x_1459_ = ((size_t)7ULL);
v___x_1460_ = lean_usize_dec_le(v___x_1459_, v_x_1395_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1461_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1451_);
v___x_1462_ = lean_unsigned_to_nat(4u);
v___x_1463_ = lean_nat_dec_lt(v___x_1461_, v___x_1462_);
lean_dec(v___x_1461_);
v___y_1453_ = v___x_1463_;
goto v___jp_1452_;
}
else
{
v___y_1453_ = v___x_1460_;
goto v___jp_1452_;
}
v___jp_1452_:
{
if (v___y_1453_ == 0)
{
lean_object* v_ks_1454_; lean_object* v_vs_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v_ks_1454_ = lean_ctor_get(v_newNode_1451_, 0);
lean_inc_ref(v_ks_1454_);
v_vs_1455_ = lean_ctor_get(v_newNode_1451_, 1);
lean_inc_ref(v_vs_1455_);
lean_dec_ref(v_newNode_1451_);
v___x_1456_ = lean_unsigned_to_nat(0u);
v___x_1457_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_1458_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_x_1395_, v_ks_1454_, v_vs_1455_, v___x_1456_, v___x_1457_);
lean_dec_ref(v_vs_1455_);
lean_dec_ref(v_ks_1454_);
return v___x_1458_;
}
else
{
return v_newNode_1451_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1466_, lean_object* v_keys_1467_, lean_object* v_vals_1468_, lean_object* v_i_1469_, lean_object* v_entries_1470_){
_start:
{
lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = lean_array_get_size(v_keys_1467_);
v___x_1472_ = lean_nat_dec_lt(v_i_1469_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_dec(v_i_1469_);
return v_entries_1470_;
}
else
{
lean_object* v_k_1473_; lean_object* v_v_1474_; uint64_t v___x_1475_; size_t v_h_1476_; size_t v___x_1477_; lean_object* v___x_1478_; size_t v___x_1479_; size_t v___x_1480_; size_t v___x_1481_; size_t v_h_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_k_1473_ = lean_array_fget_borrowed(v_keys_1467_, v_i_1469_);
v_v_1474_ = lean_array_fget_borrowed(v_vals_1468_, v_i_1469_);
v___x_1475_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1473_);
v_h_1476_ = lean_uint64_to_usize(v___x_1475_);
v___x_1477_ = ((size_t)5ULL);
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = ((size_t)1ULL);
v___x_1480_ = lean_usize_sub(v_depth_1466_, v___x_1479_);
v___x_1481_ = lean_usize_mul(v___x_1477_, v___x_1480_);
v_h_1482_ = lean_usize_shift_right(v_h_1476_, v___x_1481_);
v___x_1483_ = lean_nat_add(v_i_1469_, v___x_1478_);
lean_dec(v_i_1469_);
lean_inc(v_v_1474_);
lean_inc(v_k_1473_);
v___x_1484_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_entries_1470_, v_h_1482_, v_depth_1466_, v_k_1473_, v_v_1474_);
v_i_1469_ = v___x_1483_;
v_entries_1470_ = v___x_1484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1486_, lean_object* v_keys_1487_, lean_object* v_vals_1488_, lean_object* v_i_1489_, lean_object* v_entries_1490_){
_start:
{
size_t v_depth_boxed_1491_; lean_object* v_res_1492_; 
v_depth_boxed_1491_ = lean_unbox_usize(v_depth_1486_);
lean_dec(v_depth_1486_);
v_res_1492_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1491_, v_keys_1487_, v_vals_1488_, v_i_1489_, v_entries_1490_);
lean_dec_ref(v_vals_1488_);
lean_dec_ref(v_keys_1487_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_){
_start:
{
size_t v_x_8495__boxed_1498_; size_t v_x_8496__boxed_1499_; lean_object* v_res_1500_; 
v_x_8495__boxed_1498_ = lean_unbox_usize(v_x_1494_);
lean_dec(v_x_1494_);
v_x_8496__boxed_1499_ = lean_unbox_usize(v_x_1495_);
lean_dec(v_x_1495_);
v_res_1500_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1493_, v_x_8495__boxed_1498_, v_x_8496__boxed_1499_, v_x_1496_, v_x_1497_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(lean_object* v_x_1501_, lean_object* v_x_1502_, lean_object* v_x_1503_){
_start:
{
uint64_t v___x_1504_; size_t v___x_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1504_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1502_);
v___x_1505_ = lean_uint64_to_usize(v___x_1504_);
v___x_1506_ = ((size_t)1ULL);
v___x_1507_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1501_, v___x_1505_, v___x_1506_, v_x_1502_, v_x_1503_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___lam__0(lean_object* v_e_1508_, lean_object* v_a_1509_, lean_object* v_s_1510_){
_start:
{
lean_object* v_rings_1511_; lean_object* v_typeIdOf_1512_; lean_object* v_exprToRingId_1513_; lean_object* v_semirings_1514_; lean_object* v_stypeIdOf_1515_; lean_object* v_exprToSemiringId_1516_; lean_object* v_ncRings_1517_; lean_object* v_exprToNCRingId_1518_; lean_object* v_nctypeIdOf_1519_; lean_object* v_ncSemirings_1520_; lean_object* v_exprToNCSemiringId_1521_; lean_object* v_ncstypeIdOf_1522_; lean_object* v_steps_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1531_; 
v_rings_1511_ = lean_ctor_get(v_s_1510_, 0);
v_typeIdOf_1512_ = lean_ctor_get(v_s_1510_, 1);
v_exprToRingId_1513_ = lean_ctor_get(v_s_1510_, 2);
v_semirings_1514_ = lean_ctor_get(v_s_1510_, 3);
v_stypeIdOf_1515_ = lean_ctor_get(v_s_1510_, 4);
v_exprToSemiringId_1516_ = lean_ctor_get(v_s_1510_, 5);
v_ncRings_1517_ = lean_ctor_get(v_s_1510_, 6);
v_exprToNCRingId_1518_ = lean_ctor_get(v_s_1510_, 7);
v_nctypeIdOf_1519_ = lean_ctor_get(v_s_1510_, 8);
v_ncSemirings_1520_ = lean_ctor_get(v_s_1510_, 9);
v_exprToNCSemiringId_1521_ = lean_ctor_get(v_s_1510_, 10);
v_ncstypeIdOf_1522_ = lean_ctor_get(v_s_1510_, 11);
v_steps_1523_ = lean_ctor_get(v_s_1510_, 12);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_s_1510_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1525_ = v_s_1510_;
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_steps_1523_);
lean_inc(v_ncstypeIdOf_1522_);
lean_inc(v_exprToNCSemiringId_1521_);
lean_inc(v_ncSemirings_1520_);
lean_inc(v_nctypeIdOf_1519_);
lean_inc(v_exprToNCRingId_1518_);
lean_inc(v_ncRings_1517_);
lean_inc(v_exprToSemiringId_1516_);
lean_inc(v_stypeIdOf_1515_);
lean_inc(v_semirings_1514_);
lean_inc(v_exprToRingId_1513_);
lean_inc(v_typeIdOf_1512_);
lean_inc(v_rings_1511_);
lean_dec(v_s_1510_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
lean_inc(v_a_1509_);
v___x_1527_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_exprToSemiringId_1516_, v_e_1508_, v_a_1509_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 5, v___x_1527_);
v___x_1529_ = v___x_1525_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_rings_1511_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_typeIdOf_1512_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_exprToRingId_1513_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_semirings_1514_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_stypeIdOf_1515_);
lean_ctor_set(v_reuseFailAlloc_1530_, 5, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1530_, 6, v_ncRings_1517_);
lean_ctor_set(v_reuseFailAlloc_1530_, 7, v_exprToNCRingId_1518_);
lean_ctor_set(v_reuseFailAlloc_1530_, 8, v_nctypeIdOf_1519_);
lean_ctor_set(v_reuseFailAlloc_1530_, 9, v_ncSemirings_1520_);
lean_ctor_set(v_reuseFailAlloc_1530_, 10, v_exprToNCSemiringId_1521_);
lean_ctor_set(v_reuseFailAlloc_1530_, 11, v_ncstypeIdOf_1522_);
lean_ctor_set(v_reuseFailAlloc_1530_, 12, v_steps_1523_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___lam__0___boxed(lean_object* v_e_1532_, lean_object* v_a_1533_, lean_object* v_s_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___lam__0(v_e_1532_, v_a_1533_, v_s_1534_);
lean_dec(v_a_1533_);
return v_res_1535_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___closed__1(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___closed__0));
v___x_1538_ = l_Lean_stringToMessageData(v___x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object* v_e_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1539_, v_a_1541_, v_a_1549_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v___x_1555_);
if (lean_obj_tag(v_a_1556_) == 1)
{
lean_object* v_val_1557_; uint8_t v___x_1558_; 
v_val_1557_ = lean_ctor_get(v_a_1556_, 0);
lean_inc(v_val_1557_);
lean_dec_ref(v_a_1556_);
v___x_1558_ = lean_nat_dec_eq(v_val_1557_, v_a_1540_);
lean_dec(v_val_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1543_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; uint8_t v_verbose_1561_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref(v___x_1559_);
v_verbose_1561_ = lean_ctor_get_uint8(v_a_1560_, sizeof(void*)*11 + 15);
lean_dec(v_a_1560_);
if (v_verbose_1561_ == 0)
{
lean_dec_ref(v_e_1539_);
goto v___jp_1552_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1562_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___closed__1);
v___x_1563_ = l_Lean_indentExpr(v_e_1539_);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = l_Lean_Meta_Grind_reportIssue(v___x_1564_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_dec_ref(v___x_1565_);
goto v___jp_1552_;
}
else
{
return v___x_1565_;
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v_e_1539_);
v_a_1566_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1559_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1559_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
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
else
{
lean_dec_ref(v_e_1539_);
goto v___jp_1552_;
}
}
else
{
lean_object* v___f_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_dec(v_a_1556_);
lean_inc(v_a_1540_);
v___f_1574_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1574_, 0, v_e_1539_);
lean_closure_set(v___f_1574_, 1, v_a_1540_);
v___x_1575_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1576_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1575_, v___f_1574_, v_a_1541_);
return v___x_1576_;
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v_e_1539_);
v_a_1577_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1555_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1555_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
v___jp_1552_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_box(0);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
return v___x_1554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object* v_e_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec(v_a_1586_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object* v_00_u03b2_1599_, lean_object* v_x_1600_, lean_object* v_x_1601_, lean_object* v_x_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_x_1600_, v_x_1601_, v_x_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_1604_, lean_object* v_x_1605_, size_t v_x_1606_, size_t v_x_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1605_, v_x_1606_, v_x_1607_, v_x_1608_, v_x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_){
_start:
{
size_t v_x_8767__boxed_1617_; size_t v_x_8768__boxed_1618_; lean_object* v_res_1619_; 
v_x_8767__boxed_1617_ = lean_unbox_usize(v_x_1613_);
lean_dec(v_x_1613_);
v_x_8768__boxed_1618_ = lean_unbox_usize(v_x_1614_);
lean_dec(v_x_1614_);
v_res_1619_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(v_00_u03b2_1611_, v_x_1612_, v_x_8767__boxed_1617_, v_x_8768__boxed_1618_, v_x_1615_, v_x_1616_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1620_, lean_object* v_n_1621_, lean_object* v_k_1622_, lean_object* v_v_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v_n_1621_, v_k_1622_, v_v_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1625_, size_t v_depth_1626_, lean_object* v_keys_1627_, lean_object* v_vals_1628_, lean_object* v_heq_1629_, lean_object* v_i_1630_, lean_object* v_entries_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_1626_, v_keys_1627_, v_vals_1628_, v_i_1630_, v_entries_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1633_, lean_object* v_depth_1634_, lean_object* v_keys_1635_, lean_object* v_vals_1636_, lean_object* v_heq_1637_, lean_object* v_i_1638_, lean_object* v_entries_1639_){
_start:
{
size_t v_depth_boxed_1640_; lean_object* v_res_1641_; 
v_depth_boxed_1640_ = lean_unbox_usize(v_depth_1634_);
lean_dec(v_depth_1634_);
v_res_1641_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_1633_, v_depth_boxed_1640_, v_keys_1635_, v_vals_1636_, v_heq_1637_, v_i_1638_, v_entries_1639_);
lean_dec_ref(v_vals_1636_);
lean_dec_ref(v_keys_1635_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1643_, v_x_1644_, v_x_1645_, v_x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object* v_e_1650_, lean_object* v___f_1651_, lean_object* v___f_1652_, lean_object* v_size_1653_, lean_object* v_s_1654_){
_start:
{
lean_object* v_id_1655_; lean_object* v_type_1656_; lean_object* v_u_1657_; lean_object* v_semiringInst_1658_; lean_object* v_addFn_x3f_1659_; lean_object* v_mulFn_x3f_1660_; lean_object* v_powFn_x3f_1661_; lean_object* v_natCastFn_x3f_1662_; lean_object* v_denote_1663_; lean_object* v_vars_1664_; lean_object* v_varMap_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1674_; 
v_id_1655_ = lean_ctor_get(v_s_1654_, 0);
v_type_1656_ = lean_ctor_get(v_s_1654_, 1);
v_u_1657_ = lean_ctor_get(v_s_1654_, 2);
v_semiringInst_1658_ = lean_ctor_get(v_s_1654_, 3);
v_addFn_x3f_1659_ = lean_ctor_get(v_s_1654_, 4);
v_mulFn_x3f_1660_ = lean_ctor_get(v_s_1654_, 5);
v_powFn_x3f_1661_ = lean_ctor_get(v_s_1654_, 6);
v_natCastFn_x3f_1662_ = lean_ctor_get(v_s_1654_, 7);
v_denote_1663_ = lean_ctor_get(v_s_1654_, 8);
v_vars_1664_ = lean_ctor_get(v_s_1654_, 9);
v_varMap_1665_ = lean_ctor_get(v_s_1654_, 10);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_s_1654_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1667_ = v_s_1654_;
v_isShared_1668_ = v_isSharedCheck_1674_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_varMap_1665_);
lean_inc(v_vars_1664_);
lean_inc(v_denote_1663_);
lean_inc(v_natCastFn_x3f_1662_);
lean_inc(v_powFn_x3f_1661_);
lean_inc(v_mulFn_x3f_1660_);
lean_inc(v_addFn_x3f_1659_);
lean_inc(v_semiringInst_1658_);
lean_inc(v_u_1657_);
lean_inc(v_type_1656_);
lean_inc(v_id_1655_);
lean_dec(v_s_1654_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1674_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
lean_inc_ref(v_e_1650_);
v___x_1669_ = l_Lean_PersistentArray_push___redArg(v_vars_1664_, v_e_1650_);
v___x_1670_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1651_, v___f_1652_, v_varMap_1665_, v_e_1650_, v_size_1653_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 10, v___x_1670_);
lean_ctor_set(v___x_1667_, 9, v___x_1669_);
v___x_1672_ = v___x_1667_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_id_1655_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_type_1656_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_u_1657_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v_semiringInst_1658_);
lean_ctor_set(v_reuseFailAlloc_1673_, 4, v_addFn_x3f_1659_);
lean_ctor_set(v_reuseFailAlloc_1673_, 5, v_mulFn_x3f_1660_);
lean_ctor_set(v_reuseFailAlloc_1673_, 6, v_powFn_x3f_1661_);
lean_ctor_set(v_reuseFailAlloc_1673_, 7, v_natCastFn_x3f_1662_);
lean_ctor_set(v_reuseFailAlloc_1673_, 8, v_denote_1663_);
lean_ctor_set(v_reuseFailAlloc_1673_, 9, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1673_, 10, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object* v_toPure_1675_, lean_object* v_size_1676_, lean_object* v_____r_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_apply_2(v_toPure_1675_, lean_box(0), v_size_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object* v_e_1679_, lean_object* v_inst_1680_, lean_object* v_toBind_1681_, lean_object* v___f_1682_, lean_object* v_____r_1683_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1684_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1685_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_1685_, 0, lean_box(0));
lean_closure_set(v___x_1685_, 1, v___x_1684_);
lean_closure_set(v___x_1685_, 2, v_e_1679_);
v___x_1686_ = lean_apply_2(v_inst_1680_, lean_box(0), v___x_1685_);
v___x_1687_ = lean_apply_4(v_toBind_1681_, lean_box(0), lean_box(0), v___x_1686_, v___f_1682_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object* v_inst_1688_, lean_object* v_e_1689_, lean_object* v_toBind_1690_, lean_object* v___f_1691_, lean_object* v_____r_1692_){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_apply_1(v_inst_1688_, v_e_1689_);
v___x_1694_ = lean_apply_4(v_toBind_1690_, lean_box(0), lean_box(0), v___x_1693_, v___f_1691_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object* v___f_1695_, lean_object* v___f_1696_, lean_object* v_e_1697_, lean_object* v_toPure_1698_, lean_object* v_inst_1699_, lean_object* v_toBind_1700_, lean_object* v_inst_1701_, lean_object* v_modifySemiring_1702_, lean_object* v_s_1703_){
_start:
{
lean_object* v_vars_1704_; lean_object* v_varMap_1705_; lean_object* v___x_1706_; 
v_vars_1704_ = lean_ctor_get(v_s_1703_, 9);
lean_inc_ref(v_vars_1704_);
v_varMap_1705_ = lean_ctor_get(v_s_1703_, 10);
lean_inc_ref(v_varMap_1705_);
lean_dec_ref(v_s_1703_);
lean_inc_ref(v_e_1697_);
lean_inc_ref(v___f_1696_);
lean_inc_ref(v___f_1695_);
v___x_1706_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_1695_, v___f_1696_, v_varMap_1705_, v_e_1697_);
if (lean_obj_tag(v___x_1706_) == 1)
{
lean_object* v_val_1707_; lean_object* v___x_1708_; 
lean_dec_ref(v_vars_1704_);
lean_dec(v_modifySemiring_1702_);
lean_dec(v_inst_1701_);
lean_dec(v_toBind_1700_);
lean_dec(v_inst_1699_);
lean_dec_ref(v_e_1697_);
lean_dec_ref(v___f_1696_);
lean_dec_ref(v___f_1695_);
v_val_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_val_1707_);
lean_dec_ref(v___x_1706_);
v___x_1708_ = lean_apply_2(v_toPure_1698_, lean_box(0), v_val_1707_);
return v___x_1708_;
}
else
{
lean_object* v_size_1709_; lean_object* v___f_1710_; lean_object* v___f_1711_; lean_object* v___f_1712_; lean_object* v___f_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec(v___x_1706_);
v_size_1709_ = lean_ctor_get(v_vars_1704_, 2);
lean_inc(v_size_1709_);
lean_dec_ref(v_vars_1704_);
lean_inc(v_size_1709_);
lean_inc_ref(v_e_1697_);
v___f_1710_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1710_, 0, v_e_1697_);
lean_closure_set(v___f_1710_, 1, v___f_1695_);
lean_closure_set(v___f_1710_, 2, v___f_1696_);
lean_closure_set(v___f_1710_, 3, v_size_1709_);
v___f_1711_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1711_, 0, v_toPure_1698_);
lean_closure_set(v___f_1711_, 1, v_size_1709_);
lean_inc(v_toBind_1700_);
lean_inc_ref(v_e_1697_);
v___f_1712_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1712_, 0, v_e_1697_);
lean_closure_set(v___f_1712_, 1, v_inst_1699_);
lean_closure_set(v___f_1712_, 2, v_toBind_1700_);
lean_closure_set(v___f_1712_, 3, v___f_1711_);
lean_inc(v_toBind_1700_);
v___f_1713_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1713_, 0, v_inst_1701_);
lean_closure_set(v___f_1713_, 1, v_e_1697_);
lean_closure_set(v___f_1713_, 2, v_toBind_1700_);
lean_closure_set(v___f_1713_, 3, v___f_1712_);
v___x_1714_ = lean_apply_1(v_modifySemiring_1702_, v___f_1710_);
v___x_1715_ = lean_apply_4(v_toBind_1700_, lean_box(0), lean_box(0), v___x_1714_, v___f_1713_);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_e_1722_){
_start:
{
lean_object* v_toApplicative_1723_; lean_object* v_toBind_1724_; lean_object* v_getSemiring_1725_; lean_object* v_modifySemiring_1726_; lean_object* v_toPure_1727_; lean_object* v___f_1728_; lean_object* v___f_1729_; lean_object* v___f_1730_; lean_object* v___x_1731_; 
v_toApplicative_1723_ = lean_ctor_get(v_inst_1719_, 0);
lean_inc_ref(v_toApplicative_1723_);
v_toBind_1724_ = lean_ctor_get(v_inst_1719_, 1);
lean_inc(v_toBind_1724_);
lean_dec_ref(v_inst_1719_);
v_getSemiring_1725_ = lean_ctor_get(v_inst_1720_, 0);
lean_inc(v_getSemiring_1725_);
v_modifySemiring_1726_ = lean_ctor_get(v_inst_1720_, 1);
lean_inc(v_modifySemiring_1726_);
lean_dec_ref(v_inst_1720_);
v_toPure_1727_ = lean_ctor_get(v_toApplicative_1723_, 1);
lean_inc(v_toPure_1727_);
lean_dec_ref(v_toApplicative_1723_);
v___f_1728_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0));
v___f_1729_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1));
lean_inc(v_toBind_1724_);
v___f_1730_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1730_, 0, v___f_1728_);
lean_closure_set(v___f_1730_, 1, v___f_1729_);
lean_closure_set(v___f_1730_, 2, v_e_1722_);
lean_closure_set(v___f_1730_, 3, v_toPure_1727_);
lean_closure_set(v___f_1730_, 4, v_inst_1718_);
lean_closure_set(v___f_1730_, 5, v_toBind_1724_);
lean_closure_set(v___f_1730_, 6, v_inst_1721_);
lean_closure_set(v___f_1730_, 7, v_modifySemiring_1726_);
v___x_1731_ = lean_apply_4(v_toBind_1724_, lean_box(0), lean_box(0), v_getSemiring_1725_, v___f_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object* v_m_1732_, lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_e_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v_inst_1733_, v_inst_1734_, v_inst_1735_, v_inst_1736_, v_e_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(lean_object* v___y_1739_, lean_object* v_e_1740_, lean_object* v_size_1741_, lean_object* v_s_1742_){
_start:
{
lean_object* v_rings_1743_; lean_object* v_typeIdOf_1744_; lean_object* v_exprToRingId_1745_; lean_object* v_semirings_1746_; lean_object* v_stypeIdOf_1747_; lean_object* v_exprToSemiringId_1748_; lean_object* v_ncRings_1749_; lean_object* v_exprToNCRingId_1750_; lean_object* v_nctypeIdOf_1751_; lean_object* v_ncSemirings_1752_; lean_object* v_exprToNCSemiringId_1753_; lean_object* v_ncstypeIdOf_1754_; lean_object* v_steps_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_rings_1743_ = lean_ctor_get(v_s_1742_, 0);
v_typeIdOf_1744_ = lean_ctor_get(v_s_1742_, 1);
v_exprToRingId_1745_ = lean_ctor_get(v_s_1742_, 2);
v_semirings_1746_ = lean_ctor_get(v_s_1742_, 3);
v_stypeIdOf_1747_ = lean_ctor_get(v_s_1742_, 4);
v_exprToSemiringId_1748_ = lean_ctor_get(v_s_1742_, 5);
v_ncRings_1749_ = lean_ctor_get(v_s_1742_, 6);
v_exprToNCRingId_1750_ = lean_ctor_get(v_s_1742_, 7);
v_nctypeIdOf_1751_ = lean_ctor_get(v_s_1742_, 8);
v_ncSemirings_1752_ = lean_ctor_get(v_s_1742_, 9);
v_exprToNCSemiringId_1753_ = lean_ctor_get(v_s_1742_, 10);
v_ncstypeIdOf_1754_ = lean_ctor_get(v_s_1742_, 11);
v_steps_1755_ = lean_ctor_get(v_s_1742_, 12);
v___x_1756_ = lean_array_get_size(v_semirings_1746_);
v___x_1757_ = lean_nat_dec_lt(v___y_1739_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_dec(v_size_1741_);
lean_dec_ref(v_e_1740_);
return v_s_1742_;
}
else
{
lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1800_; 
lean_inc(v_steps_1755_);
lean_inc_ref(v_ncstypeIdOf_1754_);
lean_inc_ref(v_exprToNCSemiringId_1753_);
lean_inc_ref(v_ncSemirings_1752_);
lean_inc_ref(v_nctypeIdOf_1751_);
lean_inc_ref(v_exprToNCRingId_1750_);
lean_inc_ref(v_ncRings_1749_);
lean_inc_ref(v_exprToSemiringId_1748_);
lean_inc_ref(v_stypeIdOf_1747_);
lean_inc_ref(v_semirings_1746_);
lean_inc_ref(v_exprToRingId_1745_);
lean_inc_ref(v_typeIdOf_1744_);
lean_inc_ref(v_rings_1743_);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_s_1742_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; lean_object* v_unused_1802_; lean_object* v_unused_1803_; lean_object* v_unused_1804_; lean_object* v_unused_1805_; lean_object* v_unused_1806_; lean_object* v_unused_1807_; lean_object* v_unused_1808_; lean_object* v_unused_1809_; lean_object* v_unused_1810_; lean_object* v_unused_1811_; lean_object* v_unused_1812_; lean_object* v_unused_1813_; 
v_unused_1801_ = lean_ctor_get(v_s_1742_, 12);
lean_dec(v_unused_1801_);
v_unused_1802_ = lean_ctor_get(v_s_1742_, 11);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_s_1742_, 10);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v_s_1742_, 9);
lean_dec(v_unused_1804_);
v_unused_1805_ = lean_ctor_get(v_s_1742_, 8);
lean_dec(v_unused_1805_);
v_unused_1806_ = lean_ctor_get(v_s_1742_, 7);
lean_dec(v_unused_1806_);
v_unused_1807_ = lean_ctor_get(v_s_1742_, 6);
lean_dec(v_unused_1807_);
v_unused_1808_ = lean_ctor_get(v_s_1742_, 5);
lean_dec(v_unused_1808_);
v_unused_1809_ = lean_ctor_get(v_s_1742_, 4);
lean_dec(v_unused_1809_);
v_unused_1810_ = lean_ctor_get(v_s_1742_, 3);
lean_dec(v_unused_1810_);
v_unused_1811_ = lean_ctor_get(v_s_1742_, 2);
lean_dec(v_unused_1811_);
v_unused_1812_ = lean_ctor_get(v_s_1742_, 1);
lean_dec(v_unused_1812_);
v_unused_1813_ = lean_ctor_get(v_s_1742_, 0);
lean_dec(v_unused_1813_);
v___x_1759_ = v_s_1742_;
v_isShared_1760_ = v_isSharedCheck_1800_;
goto v_resetjp_1758_;
}
else
{
lean_dec(v_s_1742_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1800_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v_v_1761_; lean_object* v_toSemiring_1762_; lean_object* v_ringId_1763_; lean_object* v_commSemiringInst_1764_; lean_object* v_addRightCancelInst_x3f_1765_; lean_object* v_toQFn_x3f_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1799_; 
v_v_1761_ = lean_array_fget(v_semirings_1746_, v___y_1739_);
v_toSemiring_1762_ = lean_ctor_get(v_v_1761_, 0);
v_ringId_1763_ = lean_ctor_get(v_v_1761_, 1);
v_commSemiringInst_1764_ = lean_ctor_get(v_v_1761_, 2);
v_addRightCancelInst_x3f_1765_ = lean_ctor_get(v_v_1761_, 3);
v_toQFn_x3f_1766_ = lean_ctor_get(v_v_1761_, 4);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_v_1761_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1768_ = v_v_1761_;
v_isShared_1769_ = v_isSharedCheck_1799_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_toQFn_x3f_1766_);
lean_inc(v_addRightCancelInst_x3f_1765_);
lean_inc(v_commSemiringInst_1764_);
lean_inc(v_ringId_1763_);
lean_inc(v_toSemiring_1762_);
lean_dec(v_v_1761_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1799_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_id_1770_; lean_object* v_type_1771_; lean_object* v_u_1772_; lean_object* v_semiringInst_1773_; lean_object* v_addFn_x3f_1774_; lean_object* v_mulFn_x3f_1775_; lean_object* v_powFn_x3f_1776_; lean_object* v_natCastFn_x3f_1777_; lean_object* v_denote_1778_; lean_object* v_vars_1779_; lean_object* v_varMap_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1798_; 
v_id_1770_ = lean_ctor_get(v_toSemiring_1762_, 0);
v_type_1771_ = lean_ctor_get(v_toSemiring_1762_, 1);
v_u_1772_ = lean_ctor_get(v_toSemiring_1762_, 2);
v_semiringInst_1773_ = lean_ctor_get(v_toSemiring_1762_, 3);
v_addFn_x3f_1774_ = lean_ctor_get(v_toSemiring_1762_, 4);
v_mulFn_x3f_1775_ = lean_ctor_get(v_toSemiring_1762_, 5);
v_powFn_x3f_1776_ = lean_ctor_get(v_toSemiring_1762_, 6);
v_natCastFn_x3f_1777_ = lean_ctor_get(v_toSemiring_1762_, 7);
v_denote_1778_ = lean_ctor_get(v_toSemiring_1762_, 8);
v_vars_1779_ = lean_ctor_get(v_toSemiring_1762_, 9);
v_varMap_1780_ = lean_ctor_get(v_toSemiring_1762_, 10);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_toSemiring_1762_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1782_ = v_toSemiring_1762_;
v_isShared_1783_ = v_isSharedCheck_1798_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_varMap_1780_);
lean_inc(v_vars_1779_);
lean_inc(v_denote_1778_);
lean_inc(v_natCastFn_x3f_1777_);
lean_inc(v_powFn_x3f_1776_);
lean_inc(v_mulFn_x3f_1775_);
lean_inc(v_addFn_x3f_1774_);
lean_inc(v_semiringInst_1773_);
lean_inc(v_u_1772_);
lean_inc(v_type_1771_);
lean_inc(v_id_1770_);
lean_dec(v_toSemiring_1762_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1798_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v_xs_x27_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1784_ = lean_box(0);
v_xs_x27_1785_ = lean_array_fset(v_semirings_1746_, v___y_1739_, v___x_1784_);
lean_inc_ref(v_e_1740_);
v___x_1786_ = l_Lean_PersistentArray_push___redArg(v_vars_1779_, v_e_1740_);
v___x_1787_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_varMap_1780_, v_e_1740_, v_size_1741_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 10, v___x_1787_);
lean_ctor_set(v___x_1782_, 9, v___x_1786_);
v___x_1789_ = v___x_1782_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_id_1770_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_type_1771_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_u_1772_);
lean_ctor_set(v_reuseFailAlloc_1797_, 3, v_semiringInst_1773_);
lean_ctor_set(v_reuseFailAlloc_1797_, 4, v_addFn_x3f_1774_);
lean_ctor_set(v_reuseFailAlloc_1797_, 5, v_mulFn_x3f_1775_);
lean_ctor_set(v_reuseFailAlloc_1797_, 6, v_powFn_x3f_1776_);
lean_ctor_set(v_reuseFailAlloc_1797_, 7, v_natCastFn_x3f_1777_);
lean_ctor_set(v_reuseFailAlloc_1797_, 8, v_denote_1778_);
lean_ctor_set(v_reuseFailAlloc_1797_, 9, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1797_, 10, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1791_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1789_);
v___x_1791_ = v___x_1768_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1789_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_ringId_1763_);
lean_ctor_set(v_reuseFailAlloc_1796_, 2, v_commSemiringInst_1764_);
lean_ctor_set(v_reuseFailAlloc_1796_, 3, v_addRightCancelInst_x3f_1765_);
lean_ctor_set(v_reuseFailAlloc_1796_, 4, v_toQFn_x3f_1766_);
v___x_1791_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1792_ = lean_array_fset(v_xs_x27_1785_, v___y_1739_, v___x_1791_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 3, v___x_1792_);
v___x_1794_ = v___x_1759_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_rings_1743_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_typeIdOf_1744_);
lean_ctor_set(v_reuseFailAlloc_1795_, 2, v_exprToRingId_1745_);
lean_ctor_set(v_reuseFailAlloc_1795_, 3, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1795_, 4, v_stypeIdOf_1747_);
lean_ctor_set(v_reuseFailAlloc_1795_, 5, v_exprToSemiringId_1748_);
lean_ctor_set(v_reuseFailAlloc_1795_, 6, v_ncRings_1749_);
lean_ctor_set(v_reuseFailAlloc_1795_, 7, v_exprToNCRingId_1750_);
lean_ctor_set(v_reuseFailAlloc_1795_, 8, v_nctypeIdOf_1751_);
lean_ctor_set(v_reuseFailAlloc_1795_, 9, v_ncSemirings_1752_);
lean_ctor_set(v_reuseFailAlloc_1795_, 10, v_exprToNCSemiringId_1753_);
lean_ctor_set(v_reuseFailAlloc_1795_, 11, v_ncstypeIdOf_1754_);
lean_ctor_set(v_reuseFailAlloc_1795_, 12, v_steps_1755_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed(lean_object* v___y_1814_, lean_object* v_e_1815_, lean_object* v_size_1816_, lean_object* v_s_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(v___y_1814_, v_e_1815_, v_size_1816_, v_s_1817_);
lean_dec(v___y_1814_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(lean_object* v_e_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1883_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1883_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1883_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v_toSemiring_1837_; lean_object* v_vars_1838_; lean_object* v_varMap_1839_; lean_object* v___x_1840_; 
v_toSemiring_1837_ = lean_ctor_get(v_a_1833_, 0);
lean_inc_ref(v_toSemiring_1837_);
lean_dec(v_a_1833_);
v_vars_1838_ = lean_ctor_get(v_toSemiring_1837_, 9);
lean_inc_ref(v_vars_1838_);
v_varMap_1839_ = lean_ctor_get(v_toSemiring_1837_, 10);
lean_inc_ref(v_varMap_1839_);
lean_dec_ref(v_toSemiring_1837_);
v___x_1840_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_varMap_1839_, v_e_1819_);
if (lean_obj_tag(v___x_1840_) == 1)
{
lean_object* v_val_1841_; lean_object* v___x_1843_; 
lean_dec_ref(v_vars_1838_);
lean_dec_ref(v_e_1819_);
v_val_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_val_1841_);
lean_dec_ref(v___x_1840_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v_val_1841_);
v___x_1843_ = v___x_1835_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_val_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
else
{
lean_object* v_size_1845_; lean_object* v___f_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec(v___x_1840_);
lean_del_object(v___x_1835_);
v_size_1845_ = lean_ctor_get(v_vars_1838_, 2);
lean_inc(v_size_1845_);
lean_dec_ref(v_vars_1838_);
lean_inc(v_size_1845_);
lean_inc_ref(v_e_1819_);
lean_inc(v___y_1820_);
v___f_1846_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1846_, 0, v___y_1820_);
lean_closure_set(v___f_1846_, 1, v_e_1819_);
lean_closure_set(v___f_1846_, 2, v_size_1845_);
v___x_1847_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1848_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1847_, v___f_1846_, v___y_1821_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v___x_1849_; 
lean_dec_ref(v___x_1848_);
lean_inc_ref(v_e_1819_);
v___x_1849_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v___x_1850_; 
lean_dec_ref(v___x_1849_);
v___x_1850_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1847_, v_e_1819_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1850_, 0);
lean_dec(v_unused_1858_);
v___x_1852_ = v___x_1850_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v___x_1850_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v_size_1845_);
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_size_1845_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_size_1845_);
v_a_1859_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1850_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1850_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v_size_1845_);
lean_dec_ref(v_e_1819_);
v_a_1867_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1849_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1849_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v_size_1845_);
lean_dec_ref(v_e_1819_);
v_a_1875_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1848_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1848_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v_e_1819_);
v_a_1884_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1832_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1832_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___boxed(lean_object* v_e_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec(v___y_1893_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar(lean_object* v_e_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar___boxed(lean_object* v_e_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVar(v_e_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
lean_dec(v_a_1925_);
lean_dec_ref(v_a_1924_);
lean_dec(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec(v_a_1921_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object* v_a_1934_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_nat_to_int(v_a_1934_);
return v___x_1935_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object* v_msg_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; lean_object* v___f_1951_; lean_object* v___x_39892__overap_1952_; lean_object* v___x_1953_; 
v___x_1950_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0);
v___f_1951_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1951_, 0, v___x_1950_);
v___x_39892__overap_1952_ = lean_panic_fn(v___f_1951_, v_msg_1937_);
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
lean_inc(v___y_1946_);
lean_inc_ref(v___y_1945_);
lean_inc(v___y_1944_);
lean_inc_ref(v___y_1943_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1940_);
lean_inc(v___y_1939_);
lean_inc(v___y_1938_);
v___x_1953_ = lean_apply_12(v___x_39892__overap_1952_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, lean_box(0));
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object* v_msg_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v_msg_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
return v_res_1967_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0));
v___x_1970_ = l_Lean_stringToMessageData(v___x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(lean_object* v_type_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1977_; 
lean_inc_ref(v_type_1971_);
v___x_1977_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_type_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1990_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1990_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1990_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
if (lean_obj_tag(v_a_1978_) == 1)
{
lean_object* v_val_1982_; lean_object* v___x_1984_; 
lean_dec_ref(v_type_1971_);
v_val_1982_ = lean_ctor_get(v_a_1978_, 0);
lean_inc(v_val_1982_);
lean_dec_ref(v_a_1978_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v_val_1982_);
v___x_1984_ = v___x_1980_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_val_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
lean_del_object(v___x_1980_);
lean_dec(v_a_1978_);
v___x_1986_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1);
v___x_1987_ = l_Lean_indentExpr(v_type_1971_);
v___x_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_1988_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
return v___x_1989_;
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec_ref(v_type_1971_);
v_a_1991_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1977_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1977_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_type_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(lean_object* v_type_2006_, lean_object* v_u_2007_, lean_object* v_instDeclName_2008_, lean_object* v_declName_2009_, lean_object* v_expectedInst_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2023_ = lean_box(0);
lean_inc(v_u_2007_);
v___x_2024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2024_, 0, v_u_2007_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
lean_inc(v_u_2007_);
v___x_2025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2025_, 0, v_u_2007_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2026_, 0, v_u_2007_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
lean_inc_ref(v___x_2026_);
v___x_2027_ = l_Lean_mkConst(v_instDeclName_2008_, v___x_2026_);
lean_inc_ref_n(v_type_2006_, 3);
v___x_2028_ = l_Lean_mkApp3(v___x_2027_, v_type_2006_, v_type_2006_, v_type_2006_);
v___x_2029_ = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2028_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref(v___x_2029_);
lean_inc(v_a_2030_);
lean_inc(v_declName_2009_);
v___x_2031_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2009_, v_a_2030_, v_expectedInst_2010_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec_ref(v___x_2031_);
v___x_2032_ = l_Lean_mkConst(v_declName_2009_, v___x_2026_);
lean_inc_ref_n(v_type_2006_, 2);
v___x_2033_ = l_Lean_mkApp4(v___x_2032_, v_type_2006_, v_type_2006_, v_type_2006_, v_a_2030_);
lean_inc(v___y_2021_);
lean_inc_ref(v___y_2020_);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
lean_inc(v___y_2017_);
lean_inc_ref(v___y_2016_);
lean_inc(v___y_2015_);
lean_inc_ref(v___y_2014_);
lean_inc(v___y_2013_);
lean_inc(v___y_2012_);
v___x_2034_ = lean_grind_canon(v___x_2033_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref(v___x_2034_);
v___x_2036_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2035_, v___y_2017_);
return v___x_2036_;
}
else
{
return v___x_2034_;
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_a_2030_);
lean_dec_ref(v___x_2026_);
lean_dec(v_declName_2009_);
lean_dec_ref(v_type_2006_);
v_a_2037_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2031_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2031_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
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
else
{
lean_dec_ref(v___x_2026_);
lean_dec_ref(v_expectedInst_2010_);
lean_dec(v_declName_2009_);
lean_dec_ref(v_type_2006_);
return v___x_2029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_type_2045_ = _args[0];
lean_object* v_u_2046_ = _args[1];
lean_object* v_instDeclName_2047_ = _args[2];
lean_object* v_declName_2048_ = _args[3];
lean_object* v_expectedInst_2049_ = _args[4];
lean_object* v___y_2050_ = _args[5];
lean_object* v___y_2051_ = _args[6];
lean_object* v___y_2052_ = _args[7];
lean_object* v___y_2053_ = _args[8];
lean_object* v___y_2054_ = _args[9];
lean_object* v___y_2055_ = _args[10];
lean_object* v___y_2056_ = _args[11];
lean_object* v___y_2057_ = _args[12];
lean_object* v___y_2058_ = _args[13];
lean_object* v___y_2059_ = _args[14];
lean_object* v___y_2060_ = _args[15];
lean_object* v___y_2061_ = _args[16];
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2045_, v_u_2046_, v_instDeclName_2047_, v_declName_2048_, v_expectedInst_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec(v___y_2050_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object* v_a_2063_, lean_object* v_s_2064_){
_start:
{
lean_object* v_toRing_2065_; lean_object* v_invFn_x3f_2066_; lean_object* v_semiringId_x3f_2067_; lean_object* v_commSemiringInst_2068_; lean_object* v_commRingInst_2069_; lean_object* v_noZeroDivInst_x3f_2070_; lean_object* v_fieldInst_x3f_2071_; lean_object* v_denoteEntries_2072_; lean_object* v_nextId_2073_; lean_object* v_steps_2074_; lean_object* v_queue_2075_; lean_object* v_basis_2076_; lean_object* v_diseqs_2077_; uint8_t v_recheck_2078_; lean_object* v_invSet_2079_; lean_object* v_numEq0_x3f_2080_; uint8_t v_numEq0Updated_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2113_; 
v_toRing_2065_ = lean_ctor_get(v_s_2064_, 0);
v_invFn_x3f_2066_ = lean_ctor_get(v_s_2064_, 1);
v_semiringId_x3f_2067_ = lean_ctor_get(v_s_2064_, 2);
v_commSemiringInst_2068_ = lean_ctor_get(v_s_2064_, 3);
v_commRingInst_2069_ = lean_ctor_get(v_s_2064_, 4);
v_noZeroDivInst_x3f_2070_ = lean_ctor_get(v_s_2064_, 5);
v_fieldInst_x3f_2071_ = lean_ctor_get(v_s_2064_, 6);
v_denoteEntries_2072_ = lean_ctor_get(v_s_2064_, 7);
v_nextId_2073_ = lean_ctor_get(v_s_2064_, 8);
v_steps_2074_ = lean_ctor_get(v_s_2064_, 9);
v_queue_2075_ = lean_ctor_get(v_s_2064_, 10);
v_basis_2076_ = lean_ctor_get(v_s_2064_, 11);
v_diseqs_2077_ = lean_ctor_get(v_s_2064_, 12);
v_recheck_2078_ = lean_ctor_get_uint8(v_s_2064_, sizeof(void*)*15);
v_invSet_2079_ = lean_ctor_get(v_s_2064_, 13);
v_numEq0_x3f_2080_ = lean_ctor_get(v_s_2064_, 14);
v_numEq0Updated_2081_ = lean_ctor_get_uint8(v_s_2064_, sizeof(void*)*15 + 1);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_s_2064_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2083_ = v_s_2064_;
v_isShared_2084_ = v_isSharedCheck_2113_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_numEq0_x3f_2080_);
lean_inc(v_invSet_2079_);
lean_inc(v_diseqs_2077_);
lean_inc(v_basis_2076_);
lean_inc(v_queue_2075_);
lean_inc(v_steps_2074_);
lean_inc(v_nextId_2073_);
lean_inc(v_denoteEntries_2072_);
lean_inc(v_fieldInst_x3f_2071_);
lean_inc(v_noZeroDivInst_x3f_2070_);
lean_inc(v_commRingInst_2069_);
lean_inc(v_commSemiringInst_2068_);
lean_inc(v_semiringId_x3f_2067_);
lean_inc(v_invFn_x3f_2066_);
lean_inc(v_toRing_2065_);
lean_dec(v_s_2064_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2113_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_id_2085_; lean_object* v_type_2086_; lean_object* v_u_2087_; lean_object* v_ringInst_2088_; lean_object* v_semiringInst_2089_; lean_object* v_charInst_x3f_2090_; lean_object* v_addFn_x3f_2091_; lean_object* v_subFn_x3f_2092_; lean_object* v_negFn_x3f_2093_; lean_object* v_powFn_x3f_2094_; lean_object* v_intCastFn_x3f_2095_; lean_object* v_natCastFn_x3f_2096_; lean_object* v_one_x3f_2097_; lean_object* v_vars_2098_; lean_object* v_varMap_2099_; lean_object* v_denote_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2111_; 
v_id_2085_ = lean_ctor_get(v_toRing_2065_, 0);
v_type_2086_ = lean_ctor_get(v_toRing_2065_, 1);
v_u_2087_ = lean_ctor_get(v_toRing_2065_, 2);
v_ringInst_2088_ = lean_ctor_get(v_toRing_2065_, 3);
v_semiringInst_2089_ = lean_ctor_get(v_toRing_2065_, 4);
v_charInst_x3f_2090_ = lean_ctor_get(v_toRing_2065_, 5);
v_addFn_x3f_2091_ = lean_ctor_get(v_toRing_2065_, 6);
v_subFn_x3f_2092_ = lean_ctor_get(v_toRing_2065_, 8);
v_negFn_x3f_2093_ = lean_ctor_get(v_toRing_2065_, 9);
v_powFn_x3f_2094_ = lean_ctor_get(v_toRing_2065_, 10);
v_intCastFn_x3f_2095_ = lean_ctor_get(v_toRing_2065_, 11);
v_natCastFn_x3f_2096_ = lean_ctor_get(v_toRing_2065_, 12);
v_one_x3f_2097_ = lean_ctor_get(v_toRing_2065_, 13);
v_vars_2098_ = lean_ctor_get(v_toRing_2065_, 14);
v_varMap_2099_ = lean_ctor_get(v_toRing_2065_, 15);
v_denote_2100_ = lean_ctor_get(v_toRing_2065_, 16);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_toRing_2065_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v_toRing_2065_, 7);
lean_dec(v_unused_2112_);
v___x_2102_ = v_toRing_2065_;
v_isShared_2103_ = v_isSharedCheck_2111_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_denote_2100_);
lean_inc(v_varMap_2099_);
lean_inc(v_vars_2098_);
lean_inc(v_one_x3f_2097_);
lean_inc(v_natCastFn_x3f_2096_);
lean_inc(v_intCastFn_x3f_2095_);
lean_inc(v_powFn_x3f_2094_);
lean_inc(v_negFn_x3f_2093_);
lean_inc(v_subFn_x3f_2092_);
lean_inc(v_addFn_x3f_2091_);
lean_inc(v_charInst_x3f_2090_);
lean_inc(v_semiringInst_2089_);
lean_inc(v_ringInst_2088_);
lean_inc(v_u_2087_);
lean_inc(v_type_2086_);
lean_inc(v_id_2085_);
lean_dec(v_toRing_2065_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2111_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2104_, 0, v_a_2063_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 7, v___x_2104_);
v___x_2106_ = v___x_2102_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_id_2085_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_type_2086_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_u_2087_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_ringInst_2088_);
lean_ctor_set(v_reuseFailAlloc_2110_, 4, v_semiringInst_2089_);
lean_ctor_set(v_reuseFailAlloc_2110_, 5, v_charInst_x3f_2090_);
lean_ctor_set(v_reuseFailAlloc_2110_, 6, v_addFn_x3f_2091_);
lean_ctor_set(v_reuseFailAlloc_2110_, 7, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2110_, 8, v_subFn_x3f_2092_);
lean_ctor_set(v_reuseFailAlloc_2110_, 9, v_negFn_x3f_2093_);
lean_ctor_set(v_reuseFailAlloc_2110_, 10, v_powFn_x3f_2094_);
lean_ctor_set(v_reuseFailAlloc_2110_, 11, v_intCastFn_x3f_2095_);
lean_ctor_set(v_reuseFailAlloc_2110_, 12, v_natCastFn_x3f_2096_);
lean_ctor_set(v_reuseFailAlloc_2110_, 13, v_one_x3f_2097_);
lean_ctor_set(v_reuseFailAlloc_2110_, 14, v_vars_2098_);
lean_ctor_set(v_reuseFailAlloc_2110_, 15, v_varMap_2099_);
lean_ctor_set(v_reuseFailAlloc_2110_, 16, v_denote_2100_);
v___x_2106_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2106_);
v___x_2108_ = v___x_2083_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_invFn_x3f_2066_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_semiringId_x3f_2067_);
lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_commSemiringInst_2068_);
lean_ctor_set(v_reuseFailAlloc_2109_, 4, v_commRingInst_2069_);
lean_ctor_set(v_reuseFailAlloc_2109_, 5, v_noZeroDivInst_x3f_2070_);
lean_ctor_set(v_reuseFailAlloc_2109_, 6, v_fieldInst_x3f_2071_);
lean_ctor_set(v_reuseFailAlloc_2109_, 7, v_denoteEntries_2072_);
lean_ctor_set(v_reuseFailAlloc_2109_, 8, v_nextId_2073_);
lean_ctor_set(v_reuseFailAlloc_2109_, 9, v_steps_2074_);
lean_ctor_set(v_reuseFailAlloc_2109_, 10, v_queue_2075_);
lean_ctor_set(v_reuseFailAlloc_2109_, 11, v_basis_2076_);
lean_ctor_set(v_reuseFailAlloc_2109_, 12, v_diseqs_2077_);
lean_ctor_set(v_reuseFailAlloc_2109_, 13, v_invSet_2079_);
lean_ctor_set(v_reuseFailAlloc_2109_, 14, v_numEq0_x3f_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2109_, sizeof(void*)*15, v_recheck_2078_);
lean_ctor_set_uint8(v_reuseFailAlloc_2109_, sizeof(void*)*15 + 1, v_numEq0Updated_2081_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2170_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2170_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2170_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_toRing_2131_; lean_object* v_mulFn_x3f_2132_; 
v_toRing_2131_ = lean_ctor_get(v_a_2127_, 0);
lean_inc_ref(v_toRing_2131_);
lean_dec(v_a_2127_);
v_mulFn_x3f_2132_ = lean_ctor_get(v_toRing_2131_, 7);
if (lean_obj_tag(v_mulFn_x3f_2132_) == 1)
{
lean_object* v_val_2133_; lean_object* v___x_2135_; 
lean_inc_ref(v_mulFn_x3f_2132_);
lean_dec_ref(v_toRing_2131_);
v_val_2133_ = lean_ctor_get(v_mulFn_x3f_2132_, 0);
lean_inc(v_val_2133_);
lean_dec_ref(v_mulFn_x3f_2132_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v_val_2133_);
v___x_2135_ = v___x_2129_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_val_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
else
{
lean_object* v_type_2137_; lean_object* v_u_2138_; lean_object* v_semiringInst_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_expectedInst_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_del_object(v___x_2129_);
v_type_2137_ = lean_ctor_get(v_toRing_2131_, 1);
lean_inc_ref(v_type_2137_);
v_u_2138_ = lean_ctor_get(v_toRing_2131_, 2);
lean_inc(v_u_2138_);
v_semiringInst_2139_ = lean_ctor_get(v_toRing_2131_, 4);
lean_inc_ref(v_semiringInst_2139_);
lean_dec_ref(v_toRing_2131_);
v___x_2140_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_2141_ = lean_box(0);
lean_inc(v_u_2138_);
v___x_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2142_, 0, v_u_2138_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
lean_inc_ref(v___x_2142_);
v___x_2143_ = l_Lean_mkConst(v___x_2140_, v___x_2142_);
v___x_2144_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_2145_ = l_Lean_mkConst(v___x_2144_, v___x_2142_);
lean_inc_ref(v_type_2137_);
v___x_2146_ = l_Lean_mkAppB(v___x_2145_, v_type_2137_, v_semiringInst_2139_);
lean_inc_ref(v_type_2137_);
v_expectedInst_2147_ = l_Lean_mkAppB(v___x_2143_, v_type_2137_, v___x_2146_);
v___x_2148_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5));
v___x_2149_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7));
v___x_2150_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2137_, v_u_2138_, v___x_2148_, v___x_2149_, v_expectedInst_2147_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___f_2152_; lean_object* v___x_2153_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref(v___x_2150_);
lean_inc(v_a_2151_);
v___f_2152_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2152_, 0, v_a_2151_);
v___x_2153_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2152_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v___x_2153_, 0);
lean_dec(v_unused_2161_);
v___x_2155_ = v___x_2153_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_dec(v___x_2153_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v_a_2151_);
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2151_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec(v_a_2151_);
v_a_2162_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2153_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2153_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
return v___x_2150_;
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
v_a_2171_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2126_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2126_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec(v___y_2179_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object* v_a_2192_, lean_object* v_s_2193_){
_start:
{
lean_object* v_toRing_2194_; lean_object* v_invFn_x3f_2195_; lean_object* v_semiringId_x3f_2196_; lean_object* v_commSemiringInst_2197_; lean_object* v_commRingInst_2198_; lean_object* v_noZeroDivInst_x3f_2199_; lean_object* v_fieldInst_x3f_2200_; lean_object* v_denoteEntries_2201_; lean_object* v_nextId_2202_; lean_object* v_steps_2203_; lean_object* v_queue_2204_; lean_object* v_basis_2205_; lean_object* v_diseqs_2206_; uint8_t v_recheck_2207_; lean_object* v_invSet_2208_; lean_object* v_numEq0_x3f_2209_; uint8_t v_numEq0Updated_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2242_; 
v_toRing_2194_ = lean_ctor_get(v_s_2193_, 0);
v_invFn_x3f_2195_ = lean_ctor_get(v_s_2193_, 1);
v_semiringId_x3f_2196_ = lean_ctor_get(v_s_2193_, 2);
v_commSemiringInst_2197_ = lean_ctor_get(v_s_2193_, 3);
v_commRingInst_2198_ = lean_ctor_get(v_s_2193_, 4);
v_noZeroDivInst_x3f_2199_ = lean_ctor_get(v_s_2193_, 5);
v_fieldInst_x3f_2200_ = lean_ctor_get(v_s_2193_, 6);
v_denoteEntries_2201_ = lean_ctor_get(v_s_2193_, 7);
v_nextId_2202_ = lean_ctor_get(v_s_2193_, 8);
v_steps_2203_ = lean_ctor_get(v_s_2193_, 9);
v_queue_2204_ = lean_ctor_get(v_s_2193_, 10);
v_basis_2205_ = lean_ctor_get(v_s_2193_, 11);
v_diseqs_2206_ = lean_ctor_get(v_s_2193_, 12);
v_recheck_2207_ = lean_ctor_get_uint8(v_s_2193_, sizeof(void*)*15);
v_invSet_2208_ = lean_ctor_get(v_s_2193_, 13);
v_numEq0_x3f_2209_ = lean_ctor_get(v_s_2193_, 14);
v_numEq0Updated_2210_ = lean_ctor_get_uint8(v_s_2193_, sizeof(void*)*15 + 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_s_2193_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2212_ = v_s_2193_;
v_isShared_2213_ = v_isSharedCheck_2242_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_numEq0_x3f_2209_);
lean_inc(v_invSet_2208_);
lean_inc(v_diseqs_2206_);
lean_inc(v_basis_2205_);
lean_inc(v_queue_2204_);
lean_inc(v_steps_2203_);
lean_inc(v_nextId_2202_);
lean_inc(v_denoteEntries_2201_);
lean_inc(v_fieldInst_x3f_2200_);
lean_inc(v_noZeroDivInst_x3f_2199_);
lean_inc(v_commRingInst_2198_);
lean_inc(v_commSemiringInst_2197_);
lean_inc(v_semiringId_x3f_2196_);
lean_inc(v_invFn_x3f_2195_);
lean_inc(v_toRing_2194_);
lean_dec(v_s_2193_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2242_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v_id_2214_; lean_object* v_type_2215_; lean_object* v_u_2216_; lean_object* v_ringInst_2217_; lean_object* v_semiringInst_2218_; lean_object* v_charInst_x3f_2219_; lean_object* v_mulFn_x3f_2220_; lean_object* v_subFn_x3f_2221_; lean_object* v_negFn_x3f_2222_; lean_object* v_powFn_x3f_2223_; lean_object* v_intCastFn_x3f_2224_; lean_object* v_natCastFn_x3f_2225_; lean_object* v_one_x3f_2226_; lean_object* v_vars_2227_; lean_object* v_varMap_2228_; lean_object* v_denote_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2240_; 
v_id_2214_ = lean_ctor_get(v_toRing_2194_, 0);
v_type_2215_ = lean_ctor_get(v_toRing_2194_, 1);
v_u_2216_ = lean_ctor_get(v_toRing_2194_, 2);
v_ringInst_2217_ = lean_ctor_get(v_toRing_2194_, 3);
v_semiringInst_2218_ = lean_ctor_get(v_toRing_2194_, 4);
v_charInst_x3f_2219_ = lean_ctor_get(v_toRing_2194_, 5);
v_mulFn_x3f_2220_ = lean_ctor_get(v_toRing_2194_, 7);
v_subFn_x3f_2221_ = lean_ctor_get(v_toRing_2194_, 8);
v_negFn_x3f_2222_ = lean_ctor_get(v_toRing_2194_, 9);
v_powFn_x3f_2223_ = lean_ctor_get(v_toRing_2194_, 10);
v_intCastFn_x3f_2224_ = lean_ctor_get(v_toRing_2194_, 11);
v_natCastFn_x3f_2225_ = lean_ctor_get(v_toRing_2194_, 12);
v_one_x3f_2226_ = lean_ctor_get(v_toRing_2194_, 13);
v_vars_2227_ = lean_ctor_get(v_toRing_2194_, 14);
v_varMap_2228_ = lean_ctor_get(v_toRing_2194_, 15);
v_denote_2229_ = lean_ctor_get(v_toRing_2194_, 16);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_toRing_2194_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; 
v_unused_2241_ = lean_ctor_get(v_toRing_2194_, 6);
lean_dec(v_unused_2241_);
v___x_2231_ = v_toRing_2194_;
v_isShared_2232_ = v_isSharedCheck_2240_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_denote_2229_);
lean_inc(v_varMap_2228_);
lean_inc(v_vars_2227_);
lean_inc(v_one_x3f_2226_);
lean_inc(v_natCastFn_x3f_2225_);
lean_inc(v_intCastFn_x3f_2224_);
lean_inc(v_powFn_x3f_2223_);
lean_inc(v_negFn_x3f_2222_);
lean_inc(v_subFn_x3f_2221_);
lean_inc(v_mulFn_x3f_2220_);
lean_inc(v_charInst_x3f_2219_);
lean_inc(v_semiringInst_2218_);
lean_inc(v_ringInst_2217_);
lean_inc(v_u_2216_);
lean_inc(v_type_2215_);
lean_inc(v_id_2214_);
lean_dec(v_toRing_2194_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2240_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2233_, 0, v_a_2192_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 6, v___x_2233_);
v___x_2235_ = v___x_2231_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_id_2214_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_type_2215_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_u_2216_);
lean_ctor_set(v_reuseFailAlloc_2239_, 3, v_ringInst_2217_);
lean_ctor_set(v_reuseFailAlloc_2239_, 4, v_semiringInst_2218_);
lean_ctor_set(v_reuseFailAlloc_2239_, 5, v_charInst_x3f_2219_);
lean_ctor_set(v_reuseFailAlloc_2239_, 6, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2239_, 7, v_mulFn_x3f_2220_);
lean_ctor_set(v_reuseFailAlloc_2239_, 8, v_subFn_x3f_2221_);
lean_ctor_set(v_reuseFailAlloc_2239_, 9, v_negFn_x3f_2222_);
lean_ctor_set(v_reuseFailAlloc_2239_, 10, v_powFn_x3f_2223_);
lean_ctor_set(v_reuseFailAlloc_2239_, 11, v_intCastFn_x3f_2224_);
lean_ctor_set(v_reuseFailAlloc_2239_, 12, v_natCastFn_x3f_2225_);
lean_ctor_set(v_reuseFailAlloc_2239_, 13, v_one_x3f_2226_);
lean_ctor_set(v_reuseFailAlloc_2239_, 14, v_vars_2227_);
lean_ctor_set(v_reuseFailAlloc_2239_, 15, v_varMap_2228_);
lean_ctor_set(v_reuseFailAlloc_2239_, 16, v_denote_2229_);
v___x_2235_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2237_; 
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2235_);
v___x_2237_ = v___x_2212_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_invFn_x3f_2195_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_semiringId_x3f_2196_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_commSemiringInst_2197_);
lean_ctor_set(v_reuseFailAlloc_2238_, 4, v_commRingInst_2198_);
lean_ctor_set(v_reuseFailAlloc_2238_, 5, v_noZeroDivInst_x3f_2199_);
lean_ctor_set(v_reuseFailAlloc_2238_, 6, v_fieldInst_x3f_2200_);
lean_ctor_set(v_reuseFailAlloc_2238_, 7, v_denoteEntries_2201_);
lean_ctor_set(v_reuseFailAlloc_2238_, 8, v_nextId_2202_);
lean_ctor_set(v_reuseFailAlloc_2238_, 9, v_steps_2203_);
lean_ctor_set(v_reuseFailAlloc_2238_, 10, v_queue_2204_);
lean_ctor_set(v_reuseFailAlloc_2238_, 11, v_basis_2205_);
lean_ctor_set(v_reuseFailAlloc_2238_, 12, v_diseqs_2206_);
lean_ctor_set(v_reuseFailAlloc_2238_, 13, v_invSet_2208_);
lean_ctor_set(v_reuseFailAlloc_2238_, 14, v_numEq0_x3f_2209_);
lean_ctor_set_uint8(v_reuseFailAlloc_2238_, sizeof(void*)*15, v_recheck_2207_);
lean_ctor_set_uint8(v_reuseFailAlloc_2238_, sizeof(void*)*15 + 1, v_numEq0Updated_2210_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2299_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2299_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2299_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v_toRing_2260_; lean_object* v_addFn_x3f_2261_; 
v_toRing_2260_ = lean_ctor_get(v_a_2256_, 0);
lean_inc_ref(v_toRing_2260_);
lean_dec(v_a_2256_);
v_addFn_x3f_2261_ = lean_ctor_get(v_toRing_2260_, 6);
if (lean_obj_tag(v_addFn_x3f_2261_) == 1)
{
lean_object* v_val_2262_; lean_object* v___x_2264_; 
lean_inc_ref(v_addFn_x3f_2261_);
lean_dec_ref(v_toRing_2260_);
v_val_2262_ = lean_ctor_get(v_addFn_x3f_2261_, 0);
lean_inc(v_val_2262_);
lean_dec_ref(v_addFn_x3f_2261_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v_val_2262_);
v___x_2264_ = v___x_2258_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_val_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
else
{
lean_object* v_type_2266_; lean_object* v_u_2267_; lean_object* v_semiringInst_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v_expectedInst_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_del_object(v___x_2258_);
v_type_2266_ = lean_ctor_get(v_toRing_2260_, 1);
lean_inc_ref(v_type_2266_);
v_u_2267_ = lean_ctor_get(v_toRing_2260_, 2);
lean_inc(v_u_2267_);
v_semiringInst_2268_ = lean_ctor_get(v_toRing_2260_, 4);
lean_inc_ref(v_semiringInst_2268_);
lean_dec_ref(v_toRing_2260_);
v___x_2269_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_2270_ = lean_box(0);
lean_inc(v_u_2267_);
v___x_2271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2271_, 0, v_u_2267_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
lean_inc_ref(v___x_2271_);
v___x_2272_ = l_Lean_mkConst(v___x_2269_, v___x_2271_);
v___x_2273_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_2274_ = l_Lean_mkConst(v___x_2273_, v___x_2271_);
lean_inc_ref(v_type_2266_);
v___x_2275_ = l_Lean_mkAppB(v___x_2274_, v_type_2266_, v_semiringInst_2268_);
lean_inc_ref(v_type_2266_);
v_expectedInst_2276_ = l_Lean_mkAppB(v___x_2272_, v_type_2266_, v___x_2275_);
v___x_2277_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6));
v___x_2278_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8));
v___x_2279_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2266_, v_u_2267_, v___x_2277_, v___x_2278_, v_expectedInst_2276_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2279_);
lean_inc(v_a_2280_);
v___f_2281_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_2281_, 0, v_a_2280_);
v___x_2282_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2281_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; 
v_unused_2290_ = lean_ctor_get(v___x_2282_, 0);
lean_dec(v_unused_2290_);
v___x_2284_ = v___x_2282_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_dec(v___x_2282_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v_a_2280_);
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2280_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_a_2280_);
v_a_2291_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2282_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2282_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
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
else
{
return v___x_2279_;
}
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
v_a_2300_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2255_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2255_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec(v___y_2308_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(lean_object* v_type_2321_, lean_object* v_u_2322_, lean_object* v_instDeclName_2323_, lean_object* v_declName_2324_, lean_object* v_expectedInst_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2338_ = lean_box(0);
v___x_2339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2339_, 0, v_u_2322_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
lean_inc_ref(v___x_2339_);
v___x_2340_ = l_Lean_mkConst(v_instDeclName_2323_, v___x_2339_);
lean_inc_ref(v_type_2321_);
v___x_2341_ = l_Lean_Expr_app___override(v___x_2340_, v_type_2321_);
v___x_2342_ = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2341_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2344_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2342_);
lean_inc(v_a_2343_);
lean_inc(v_declName_2324_);
v___x_2344_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2324_, v_a_2343_, v_expectedInst_2325_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_dec_ref(v___x_2344_);
v___x_2345_ = l_Lean_mkConst(v_declName_2324_, v___x_2339_);
v___x_2346_ = l_Lean_mkAppB(v___x_2345_, v_type_2321_, v_a_2343_);
lean_inc(v___y_2336_);
lean_inc_ref(v___y_2335_);
lean_inc(v___y_2334_);
lean_inc_ref(v___y_2333_);
lean_inc(v___y_2332_);
lean_inc_ref(v___y_2331_);
lean_inc(v___y_2330_);
lean_inc_ref(v___y_2329_);
lean_inc(v___y_2328_);
lean_inc(v___y_2327_);
v___x_2347_ = lean_grind_canon(v___x_2346_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2349_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref(v___x_2347_);
v___x_2349_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2348_, v___y_2332_);
return v___x_2349_;
}
else
{
return v___x_2347_;
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v_a_2343_);
lean_dec_ref(v___x_2339_);
lean_dec(v_declName_2324_);
lean_dec_ref(v_type_2321_);
v_a_2350_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2344_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2344_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_dec_ref(v___x_2339_);
lean_dec_ref(v_expectedInst_2325_);
lean_dec(v_declName_2324_);
lean_dec_ref(v_type_2321_);
return v___x_2342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_type_2358_ = _args[0];
lean_object* v_u_2359_ = _args[1];
lean_object* v_instDeclName_2360_ = _args[2];
lean_object* v_declName_2361_ = _args[3];
lean_object* v_expectedInst_2362_ = _args[4];
lean_object* v___y_2363_ = _args[5];
lean_object* v___y_2364_ = _args[6];
lean_object* v___y_2365_ = _args[7];
lean_object* v___y_2366_ = _args[8];
lean_object* v___y_2367_ = _args[9];
lean_object* v___y_2368_ = _args[10];
lean_object* v___y_2369_ = _args[11];
lean_object* v___y_2370_ = _args[12];
lean_object* v___y_2371_ = _args[13];
lean_object* v___y_2372_ = _args[14];
lean_object* v___y_2373_ = _args[15];
lean_object* v___y_2374_ = _args[16];
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2358_, v_u_2359_, v_instDeclName_2360_, v_declName_2361_, v_expectedInst_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec(v___y_2363_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object* v_a_2376_, lean_object* v_s_2377_){
_start:
{
lean_object* v_toRing_2378_; lean_object* v_invFn_x3f_2379_; lean_object* v_semiringId_x3f_2380_; lean_object* v_commSemiringInst_2381_; lean_object* v_commRingInst_2382_; lean_object* v_noZeroDivInst_x3f_2383_; lean_object* v_fieldInst_x3f_2384_; lean_object* v_denoteEntries_2385_; lean_object* v_nextId_2386_; lean_object* v_steps_2387_; lean_object* v_queue_2388_; lean_object* v_basis_2389_; lean_object* v_diseqs_2390_; uint8_t v_recheck_2391_; lean_object* v_invSet_2392_; lean_object* v_numEq0_x3f_2393_; uint8_t v_numEq0Updated_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2426_; 
v_toRing_2378_ = lean_ctor_get(v_s_2377_, 0);
v_invFn_x3f_2379_ = lean_ctor_get(v_s_2377_, 1);
v_semiringId_x3f_2380_ = lean_ctor_get(v_s_2377_, 2);
v_commSemiringInst_2381_ = lean_ctor_get(v_s_2377_, 3);
v_commRingInst_2382_ = lean_ctor_get(v_s_2377_, 4);
v_noZeroDivInst_x3f_2383_ = lean_ctor_get(v_s_2377_, 5);
v_fieldInst_x3f_2384_ = lean_ctor_get(v_s_2377_, 6);
v_denoteEntries_2385_ = lean_ctor_get(v_s_2377_, 7);
v_nextId_2386_ = lean_ctor_get(v_s_2377_, 8);
v_steps_2387_ = lean_ctor_get(v_s_2377_, 9);
v_queue_2388_ = lean_ctor_get(v_s_2377_, 10);
v_basis_2389_ = lean_ctor_get(v_s_2377_, 11);
v_diseqs_2390_ = lean_ctor_get(v_s_2377_, 12);
v_recheck_2391_ = lean_ctor_get_uint8(v_s_2377_, sizeof(void*)*15);
v_invSet_2392_ = lean_ctor_get(v_s_2377_, 13);
v_numEq0_x3f_2393_ = lean_ctor_get(v_s_2377_, 14);
v_numEq0Updated_2394_ = lean_ctor_get_uint8(v_s_2377_, sizeof(void*)*15 + 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_s_2377_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2396_ = v_s_2377_;
v_isShared_2397_ = v_isSharedCheck_2426_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_numEq0_x3f_2393_);
lean_inc(v_invSet_2392_);
lean_inc(v_diseqs_2390_);
lean_inc(v_basis_2389_);
lean_inc(v_queue_2388_);
lean_inc(v_steps_2387_);
lean_inc(v_nextId_2386_);
lean_inc(v_denoteEntries_2385_);
lean_inc(v_fieldInst_x3f_2384_);
lean_inc(v_noZeroDivInst_x3f_2383_);
lean_inc(v_commRingInst_2382_);
lean_inc(v_commSemiringInst_2381_);
lean_inc(v_semiringId_x3f_2380_);
lean_inc(v_invFn_x3f_2379_);
lean_inc(v_toRing_2378_);
lean_dec(v_s_2377_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2426_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_id_2398_; lean_object* v_type_2399_; lean_object* v_u_2400_; lean_object* v_ringInst_2401_; lean_object* v_semiringInst_2402_; lean_object* v_charInst_x3f_2403_; lean_object* v_addFn_x3f_2404_; lean_object* v_mulFn_x3f_2405_; lean_object* v_subFn_x3f_2406_; lean_object* v_powFn_x3f_2407_; lean_object* v_intCastFn_x3f_2408_; lean_object* v_natCastFn_x3f_2409_; lean_object* v_one_x3f_2410_; lean_object* v_vars_2411_; lean_object* v_varMap_2412_; lean_object* v_denote_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2424_; 
v_id_2398_ = lean_ctor_get(v_toRing_2378_, 0);
v_type_2399_ = lean_ctor_get(v_toRing_2378_, 1);
v_u_2400_ = lean_ctor_get(v_toRing_2378_, 2);
v_ringInst_2401_ = lean_ctor_get(v_toRing_2378_, 3);
v_semiringInst_2402_ = lean_ctor_get(v_toRing_2378_, 4);
v_charInst_x3f_2403_ = lean_ctor_get(v_toRing_2378_, 5);
v_addFn_x3f_2404_ = lean_ctor_get(v_toRing_2378_, 6);
v_mulFn_x3f_2405_ = lean_ctor_get(v_toRing_2378_, 7);
v_subFn_x3f_2406_ = lean_ctor_get(v_toRing_2378_, 8);
v_powFn_x3f_2407_ = lean_ctor_get(v_toRing_2378_, 10);
v_intCastFn_x3f_2408_ = lean_ctor_get(v_toRing_2378_, 11);
v_natCastFn_x3f_2409_ = lean_ctor_get(v_toRing_2378_, 12);
v_one_x3f_2410_ = lean_ctor_get(v_toRing_2378_, 13);
v_vars_2411_ = lean_ctor_get(v_toRing_2378_, 14);
v_varMap_2412_ = lean_ctor_get(v_toRing_2378_, 15);
v_denote_2413_ = lean_ctor_get(v_toRing_2378_, 16);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_toRing_2378_);
if (v_isSharedCheck_2424_ == 0)
{
lean_object* v_unused_2425_; 
v_unused_2425_ = lean_ctor_get(v_toRing_2378_, 9);
lean_dec(v_unused_2425_);
v___x_2415_ = v_toRing_2378_;
v_isShared_2416_ = v_isSharedCheck_2424_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_denote_2413_);
lean_inc(v_varMap_2412_);
lean_inc(v_vars_2411_);
lean_inc(v_one_x3f_2410_);
lean_inc(v_natCastFn_x3f_2409_);
lean_inc(v_intCastFn_x3f_2408_);
lean_inc(v_powFn_x3f_2407_);
lean_inc(v_subFn_x3f_2406_);
lean_inc(v_mulFn_x3f_2405_);
lean_inc(v_addFn_x3f_2404_);
lean_inc(v_charInst_x3f_2403_);
lean_inc(v_semiringInst_2402_);
lean_inc(v_ringInst_2401_);
lean_inc(v_u_2400_);
lean_inc(v_type_2399_);
lean_inc(v_id_2398_);
lean_dec(v_toRing_2378_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2424_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v_a_2376_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 9, v___x_2417_);
v___x_2419_ = v___x_2415_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_id_2398_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_type_2399_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_u_2400_);
lean_ctor_set(v_reuseFailAlloc_2423_, 3, v_ringInst_2401_);
lean_ctor_set(v_reuseFailAlloc_2423_, 4, v_semiringInst_2402_);
lean_ctor_set(v_reuseFailAlloc_2423_, 5, v_charInst_x3f_2403_);
lean_ctor_set(v_reuseFailAlloc_2423_, 6, v_addFn_x3f_2404_);
lean_ctor_set(v_reuseFailAlloc_2423_, 7, v_mulFn_x3f_2405_);
lean_ctor_set(v_reuseFailAlloc_2423_, 8, v_subFn_x3f_2406_);
lean_ctor_set(v_reuseFailAlloc_2423_, 9, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2423_, 10, v_powFn_x3f_2407_);
lean_ctor_set(v_reuseFailAlloc_2423_, 11, v_intCastFn_x3f_2408_);
lean_ctor_set(v_reuseFailAlloc_2423_, 12, v_natCastFn_x3f_2409_);
lean_ctor_set(v_reuseFailAlloc_2423_, 13, v_one_x3f_2410_);
lean_ctor_set(v_reuseFailAlloc_2423_, 14, v_vars_2411_);
lean_ctor_set(v_reuseFailAlloc_2423_, 15, v_varMap_2412_);
lean_ctor_set(v_reuseFailAlloc_2423_, 16, v_denote_2413_);
v___x_2419_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2421_; 
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2419_);
v___x_2421_ = v___x_2396_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_invFn_x3f_2379_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_semiringId_x3f_2380_);
lean_ctor_set(v_reuseFailAlloc_2422_, 3, v_commSemiringInst_2381_);
lean_ctor_set(v_reuseFailAlloc_2422_, 4, v_commRingInst_2382_);
lean_ctor_set(v_reuseFailAlloc_2422_, 5, v_noZeroDivInst_x3f_2383_);
lean_ctor_set(v_reuseFailAlloc_2422_, 6, v_fieldInst_x3f_2384_);
lean_ctor_set(v_reuseFailAlloc_2422_, 7, v_denoteEntries_2385_);
lean_ctor_set(v_reuseFailAlloc_2422_, 8, v_nextId_2386_);
lean_ctor_set(v_reuseFailAlloc_2422_, 9, v_steps_2387_);
lean_ctor_set(v_reuseFailAlloc_2422_, 10, v_queue_2388_);
lean_ctor_set(v_reuseFailAlloc_2422_, 11, v_basis_2389_);
lean_ctor_set(v_reuseFailAlloc_2422_, 12, v_diseqs_2390_);
lean_ctor_set(v_reuseFailAlloc_2422_, 13, v_invSet_2392_);
lean_ctor_set(v_reuseFailAlloc_2422_, 14, v_numEq0_x3f_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2422_, sizeof(void*)*15, v_recheck_2391_);
lean_ctor_set_uint8(v_reuseFailAlloc_2422_, sizeof(void*)*15 + 1, v_numEq0Updated_2394_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2493_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2493_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2493_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_toRing_2457_; lean_object* v_negFn_x3f_2458_; 
v_toRing_2457_ = lean_ctor_get(v_a_2453_, 0);
lean_inc_ref(v_toRing_2457_);
lean_dec(v_a_2453_);
v_negFn_x3f_2458_ = lean_ctor_get(v_toRing_2457_, 9);
if (lean_obj_tag(v_negFn_x3f_2458_) == 1)
{
lean_object* v_val_2459_; lean_object* v___x_2461_; 
lean_inc_ref(v_negFn_x3f_2458_);
lean_dec_ref(v_toRing_2457_);
v_val_2459_ = lean_ctor_get(v_negFn_x3f_2458_, 0);
lean_inc(v_val_2459_);
lean_dec_ref(v_negFn_x3f_2458_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v_val_2459_);
v___x_2461_ = v___x_2455_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_val_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
else
{
lean_object* v_type_2463_; lean_object* v_u_2464_; lean_object* v_ringInst_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v_expectedInst_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_del_object(v___x_2455_);
v_type_2463_ = lean_ctor_get(v_toRing_2457_, 1);
lean_inc_ref(v_type_2463_);
v_u_2464_ = lean_ctor_get(v_toRing_2457_, 2);
lean_inc(v_u_2464_);
v_ringInst_2465_ = lean_ctor_get(v_toRing_2457_, 3);
lean_inc_ref(v_ringInst_2465_);
lean_dec_ref(v_toRing_2457_);
v___x_2466_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1));
v___x_2467_ = lean_box(0);
lean_inc(v_u_2464_);
v___x_2468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2468_, 0, v_u_2464_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = l_Lean_mkConst(v___x_2466_, v___x_2468_);
lean_inc_ref(v_type_2463_);
v_expectedInst_2470_ = l_Lean_mkAppB(v___x_2469_, v_type_2463_, v_ringInst_2465_);
v___x_2471_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3));
v___x_2472_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5));
v___x_2473_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2463_, v_u_2464_, v___x_2471_, v___x_2472_, v_expectedInst_2470_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___f_2475_; lean_object* v___x_2476_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref(v___x_2473_);
lean_inc(v_a_2474_);
v___f_2475_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_2475_, 0, v_a_2474_);
v___x_2476_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2475_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v___x_2476_, 0);
lean_dec(v_unused_2484_);
v___x_2478_ = v___x_2476_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_dec(v___x_2476_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 0, v_a_2474_);
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2474_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v_a_2474_);
v_a_2485_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2476_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2476_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
else
{
return v___x_2473_;
}
}
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
v_a_2494_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2452_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2452_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec(v___y_2502_);
return v_res_2514_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = lean_nat_to_int(v___x_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(lean_object* v_k_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v_toRing_2544_; lean_object* v_type_2545_; lean_object* v_u_2546_; lean_object* v_semiringInst_2547_; lean_object* v___x_2548_; lean_object* v_n_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref(v___x_2542_);
v_toRing_2544_ = lean_ctor_get(v_a_2543_, 0);
lean_inc_ref(v_toRing_2544_);
lean_dec(v_a_2543_);
v_type_2545_ = lean_ctor_get(v_toRing_2544_, 1);
lean_inc_ref(v_type_2545_);
v_u_2546_ = lean_ctor_get(v_toRing_2544_, 2);
lean_inc(v_u_2546_);
v_semiringInst_2547_ = lean_ctor_get(v_toRing_2544_, 4);
lean_inc_ref(v_semiringInst_2547_);
lean_dec_ref(v_toRing_2544_);
v___x_2548_ = lean_nat_abs(v_k_2529_);
v_n_2549_ = l_Lean_mkRawNatLit(v___x_2548_);
v___x_2550_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1));
v___x_2551_ = lean_box(0);
v___x_2552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2552_, 0, v_u_2546_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
lean_inc_ref(v___x_2552_);
v___x_2553_ = l_Lean_mkConst(v___x_2550_, v___x_2552_);
lean_inc_ref(v_n_2549_);
lean_inc_ref(v_type_2545_);
v___x_2554_ = l_Lean_mkAppB(v___x_2553_, v_type_2545_, v_n_2549_);
v___x_2555_ = lean_box(0);
v___x_2556_ = l_Lean_Meta_synthInstance_x3f(v___x_2554_, v___x_2555_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2596_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2596_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2596_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v_ofNatInst_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; 
if (lean_obj_tag(v_a_2557_) == 1)
{
lean_object* v_val_2592_; 
lean_dec_ref(v_semiringInst_2547_);
v_val_2592_ = lean_ctor_get(v_a_2557_, 0);
lean_inc(v_val_2592_);
lean_dec_ref(v_a_2557_);
v_ofNatInst_2562_ = v_val_2592_;
v___y_2563_ = v___y_2530_;
v___y_2564_ = v___y_2531_;
v___y_2565_ = v___y_2532_;
v___y_2566_ = v___y_2533_;
v___y_2567_ = v___y_2534_;
v___y_2568_ = v___y_2535_;
v___y_2569_ = v___y_2536_;
v___y_2570_ = v___y_2537_;
v___y_2571_ = v___y_2538_;
v___y_2572_ = v___y_2539_;
v___y_2573_ = v___y_2540_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
lean_dec(v_a_2557_);
v___x_2593_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5));
lean_inc_ref(v___x_2552_);
v___x_2594_ = l_Lean_mkConst(v___x_2593_, v___x_2552_);
lean_inc_ref(v_n_2549_);
lean_inc_ref(v_type_2545_);
v___x_2595_ = l_Lean_mkApp3(v___x_2594_, v_type_2545_, v_semiringInst_2547_, v_n_2549_);
v_ofNatInst_2562_ = v___x_2595_;
v___y_2563_ = v___y_2530_;
v___y_2564_ = v___y_2531_;
v___y_2565_ = v___y_2532_;
v___y_2566_ = v___y_2533_;
v___y_2567_ = v___y_2534_;
v___y_2568_ = v___y_2535_;
v___y_2569_ = v___y_2536_;
v___y_2570_ = v___y_2537_;
v___y_2571_ = v___y_2538_;
v___y_2572_ = v___y_2539_;
v___y_2573_ = v___y_2540_;
goto v___jp_2561_;
}
v___jp_2561_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v_n_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2574_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3));
v___x_2575_ = l_Lean_mkConst(v___x_2574_, v___x_2552_);
v_n_2576_ = l_Lean_mkApp3(v___x_2575_, v_type_2545_, v_n_2549_, v_ofNatInst_2562_);
v___x_2577_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4);
v___x_2578_ = lean_int_dec_lt(v_k_2529_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2580_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v_n_2576_);
v___x_2580_ = v___x_2559_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_n_2576_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
else
{
lean_object* v___x_2582_; 
lean_del_object(v___x_2559_);
v___x_2582_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2591_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2591_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2591_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2587_ = l_Lean_Expr_app___override(v_a_2583_, v_n_2576_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2587_);
v___x_2589_ = v___x_2585_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
else
{
lean_dec_ref(v_n_2576_);
return v___x_2582_;
}
}
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec_ref(v___x_2552_);
lean_dec_ref(v_n_2549_);
lean_dec_ref(v_semiringInst_2547_);
lean_dec_ref(v_type_2545_);
v_a_2597_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2556_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2556_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
v_a_2605_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2542_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2542_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(lean_object* v_k_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec(v_k_2613_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(lean_object* v_a_2627_, lean_object* v_s_2628_){
_start:
{
lean_object* v_toRing_2629_; lean_object* v_invFn_x3f_2630_; lean_object* v_semiringId_x3f_2631_; lean_object* v_commSemiringInst_2632_; lean_object* v_commRingInst_2633_; lean_object* v_noZeroDivInst_x3f_2634_; lean_object* v_fieldInst_x3f_2635_; lean_object* v_denoteEntries_2636_; lean_object* v_nextId_2637_; lean_object* v_steps_2638_; lean_object* v_queue_2639_; lean_object* v_basis_2640_; lean_object* v_diseqs_2641_; uint8_t v_recheck_2642_; lean_object* v_invSet_2643_; lean_object* v_numEq0_x3f_2644_; uint8_t v_numEq0Updated_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2677_; 
v_toRing_2629_ = lean_ctor_get(v_s_2628_, 0);
v_invFn_x3f_2630_ = lean_ctor_get(v_s_2628_, 1);
v_semiringId_x3f_2631_ = lean_ctor_get(v_s_2628_, 2);
v_commSemiringInst_2632_ = lean_ctor_get(v_s_2628_, 3);
v_commRingInst_2633_ = lean_ctor_get(v_s_2628_, 4);
v_noZeroDivInst_x3f_2634_ = lean_ctor_get(v_s_2628_, 5);
v_fieldInst_x3f_2635_ = lean_ctor_get(v_s_2628_, 6);
v_denoteEntries_2636_ = lean_ctor_get(v_s_2628_, 7);
v_nextId_2637_ = lean_ctor_get(v_s_2628_, 8);
v_steps_2638_ = lean_ctor_get(v_s_2628_, 9);
v_queue_2639_ = lean_ctor_get(v_s_2628_, 10);
v_basis_2640_ = lean_ctor_get(v_s_2628_, 11);
v_diseqs_2641_ = lean_ctor_get(v_s_2628_, 12);
v_recheck_2642_ = lean_ctor_get_uint8(v_s_2628_, sizeof(void*)*15);
v_invSet_2643_ = lean_ctor_get(v_s_2628_, 13);
v_numEq0_x3f_2644_ = lean_ctor_get(v_s_2628_, 14);
v_numEq0Updated_2645_ = lean_ctor_get_uint8(v_s_2628_, sizeof(void*)*15 + 1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_s_2628_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2647_ = v_s_2628_;
v_isShared_2648_ = v_isSharedCheck_2677_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_numEq0_x3f_2644_);
lean_inc(v_invSet_2643_);
lean_inc(v_diseqs_2641_);
lean_inc(v_basis_2640_);
lean_inc(v_queue_2639_);
lean_inc(v_steps_2638_);
lean_inc(v_nextId_2637_);
lean_inc(v_denoteEntries_2636_);
lean_inc(v_fieldInst_x3f_2635_);
lean_inc(v_noZeroDivInst_x3f_2634_);
lean_inc(v_commRingInst_2633_);
lean_inc(v_commSemiringInst_2632_);
lean_inc(v_semiringId_x3f_2631_);
lean_inc(v_invFn_x3f_2630_);
lean_inc(v_toRing_2629_);
lean_dec(v_s_2628_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2677_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v_id_2649_; lean_object* v_type_2650_; lean_object* v_u_2651_; lean_object* v_ringInst_2652_; lean_object* v_semiringInst_2653_; lean_object* v_charInst_x3f_2654_; lean_object* v_addFn_x3f_2655_; lean_object* v_mulFn_x3f_2656_; lean_object* v_subFn_x3f_2657_; lean_object* v_negFn_x3f_2658_; lean_object* v_intCastFn_x3f_2659_; lean_object* v_natCastFn_x3f_2660_; lean_object* v_one_x3f_2661_; lean_object* v_vars_2662_; lean_object* v_varMap_2663_; lean_object* v_denote_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2675_; 
v_id_2649_ = lean_ctor_get(v_toRing_2629_, 0);
v_type_2650_ = lean_ctor_get(v_toRing_2629_, 1);
v_u_2651_ = lean_ctor_get(v_toRing_2629_, 2);
v_ringInst_2652_ = lean_ctor_get(v_toRing_2629_, 3);
v_semiringInst_2653_ = lean_ctor_get(v_toRing_2629_, 4);
v_charInst_x3f_2654_ = lean_ctor_get(v_toRing_2629_, 5);
v_addFn_x3f_2655_ = lean_ctor_get(v_toRing_2629_, 6);
v_mulFn_x3f_2656_ = lean_ctor_get(v_toRing_2629_, 7);
v_subFn_x3f_2657_ = lean_ctor_get(v_toRing_2629_, 8);
v_negFn_x3f_2658_ = lean_ctor_get(v_toRing_2629_, 9);
v_intCastFn_x3f_2659_ = lean_ctor_get(v_toRing_2629_, 11);
v_natCastFn_x3f_2660_ = lean_ctor_get(v_toRing_2629_, 12);
v_one_x3f_2661_ = lean_ctor_get(v_toRing_2629_, 13);
v_vars_2662_ = lean_ctor_get(v_toRing_2629_, 14);
v_varMap_2663_ = lean_ctor_get(v_toRing_2629_, 15);
v_denote_2664_ = lean_ctor_get(v_toRing_2629_, 16);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_toRing_2629_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; 
v_unused_2676_ = lean_ctor_get(v_toRing_2629_, 10);
lean_dec(v_unused_2676_);
v___x_2666_ = v_toRing_2629_;
v_isShared_2667_ = v_isSharedCheck_2675_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_denote_2664_);
lean_inc(v_varMap_2663_);
lean_inc(v_vars_2662_);
lean_inc(v_one_x3f_2661_);
lean_inc(v_natCastFn_x3f_2660_);
lean_inc(v_intCastFn_x3f_2659_);
lean_inc(v_negFn_x3f_2658_);
lean_inc(v_subFn_x3f_2657_);
lean_inc(v_mulFn_x3f_2656_);
lean_inc(v_addFn_x3f_2655_);
lean_inc(v_charInst_x3f_2654_);
lean_inc(v_semiringInst_2653_);
lean_inc(v_ringInst_2652_);
lean_inc(v_u_2651_);
lean_inc(v_type_2650_);
lean_inc(v_id_2649_);
lean_dec(v_toRing_2629_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2675_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_a_2627_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 10, v___x_2668_);
v___x_2670_ = v___x_2666_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_id_2649_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_type_2650_);
lean_ctor_set(v_reuseFailAlloc_2674_, 2, v_u_2651_);
lean_ctor_set(v_reuseFailAlloc_2674_, 3, v_ringInst_2652_);
lean_ctor_set(v_reuseFailAlloc_2674_, 4, v_semiringInst_2653_);
lean_ctor_set(v_reuseFailAlloc_2674_, 5, v_charInst_x3f_2654_);
lean_ctor_set(v_reuseFailAlloc_2674_, 6, v_addFn_x3f_2655_);
lean_ctor_set(v_reuseFailAlloc_2674_, 7, v_mulFn_x3f_2656_);
lean_ctor_set(v_reuseFailAlloc_2674_, 8, v_subFn_x3f_2657_);
lean_ctor_set(v_reuseFailAlloc_2674_, 9, v_negFn_x3f_2658_);
lean_ctor_set(v_reuseFailAlloc_2674_, 10, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2674_, 11, v_intCastFn_x3f_2659_);
lean_ctor_set(v_reuseFailAlloc_2674_, 12, v_natCastFn_x3f_2660_);
lean_ctor_set(v_reuseFailAlloc_2674_, 13, v_one_x3f_2661_);
lean_ctor_set(v_reuseFailAlloc_2674_, 14, v_vars_2662_);
lean_ctor_set(v_reuseFailAlloc_2674_, 15, v_varMap_2663_);
lean_ctor_set(v_reuseFailAlloc_2674_, 16, v_denote_2664_);
v___x_2670_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2672_; 
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2670_);
v___x_2672_ = v___x_2647_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_invFn_x3f_2630_);
lean_ctor_set(v_reuseFailAlloc_2673_, 2, v_semiringId_x3f_2631_);
lean_ctor_set(v_reuseFailAlloc_2673_, 3, v_commSemiringInst_2632_);
lean_ctor_set(v_reuseFailAlloc_2673_, 4, v_commRingInst_2633_);
lean_ctor_set(v_reuseFailAlloc_2673_, 5, v_noZeroDivInst_x3f_2634_);
lean_ctor_set(v_reuseFailAlloc_2673_, 6, v_fieldInst_x3f_2635_);
lean_ctor_set(v_reuseFailAlloc_2673_, 7, v_denoteEntries_2636_);
lean_ctor_set(v_reuseFailAlloc_2673_, 8, v_nextId_2637_);
lean_ctor_set(v_reuseFailAlloc_2673_, 9, v_steps_2638_);
lean_ctor_set(v_reuseFailAlloc_2673_, 10, v_queue_2639_);
lean_ctor_set(v_reuseFailAlloc_2673_, 11, v_basis_2640_);
lean_ctor_set(v_reuseFailAlloc_2673_, 12, v_diseqs_2641_);
lean_ctor_set(v_reuseFailAlloc_2673_, 13, v_invSet_2643_);
lean_ctor_set(v_reuseFailAlloc_2673_, 14, v_numEq0_x3f_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, sizeof(void*)*15, v_recheck_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, sizeof(void*)*15 + 1, v_numEq0Updated_2645_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2681_ = lean_unsigned_to_nat(0u);
v___x_2682_ = l_Lean_Level_ofNat(v___x_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(lean_object* v_u_2693_, lean_object* v_type_2694_, lean_object* v_semiringInst_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2708_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1));
v___x_2709_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2);
v___x_2710_ = lean_box(0);
lean_inc(v_u_2693_);
v___x_2711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2711_, 0, v_u_2693_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
lean_inc_ref(v___x_2711_);
v___x_2712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2709_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2713_, 0, v_u_2693_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
lean_inc_ref(v___x_2713_);
v___x_2714_ = l_Lean_mkConst(v___x_2708_, v___x_2713_);
v___x_2715_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2694_, 2);
v___x_2716_ = l_Lean_mkApp3(v___x_2714_, v_type_2694_, v___x_2715_, v_type_2694_);
v___x_2717_ = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2716_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v_inst_x27_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref(v___x_2717_);
v___x_2719_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4));
v___x_2720_ = l_Lean_mkConst(v___x_2719_, v___x_2711_);
lean_inc_ref(v_type_2694_);
v_inst_x27_2721_ = l_Lean_mkAppB(v___x_2720_, v_type_2694_, v_semiringInst_2695_);
v___x_2722_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6));
lean_inc(v_a_2718_);
v___x_2723_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_2722_, v_a_2718_, v_inst_x27_2721_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_dec_ref(v___x_2723_);
v___x_2724_ = l_Lean_mkConst(v___x_2722_, v___x_2713_);
lean_inc_ref(v_type_2694_);
v___x_2725_ = l_Lean_mkApp4(v___x_2724_, v_type_2694_, v___x_2715_, v_type_2694_, v_a_2718_);
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
lean_inc(v___y_2704_);
lean_inc_ref(v___y_2703_);
lean_inc(v___y_2702_);
lean_inc_ref(v___y_2701_);
lean_inc(v___y_2700_);
lean_inc_ref(v___y_2699_);
lean_inc(v___y_2698_);
lean_inc(v___y_2697_);
v___x_2726_ = lean_grind_canon(v___x_2725_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2728_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref(v___x_2726_);
v___x_2728_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2727_, v___y_2702_);
return v___x_2728_;
}
else
{
return v___x_2726_;
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec(v_a_2718_);
lean_dec_ref(v___x_2713_);
lean_dec_ref(v_type_2694_);
v_a_2729_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2723_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2723_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
else
{
lean_dec_ref(v___x_2713_);
lean_dec_ref(v___x_2711_);
lean_dec_ref(v_semiringInst_2695_);
lean_dec_ref(v_type_2694_);
return v___x_2717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___boxed(lean_object* v_u_2737_, lean_object* v_type_2738_, lean_object* v_semiringInst_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2737_, v_type_2738_, v_semiringInst_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2799_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2799_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2799_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v_toRing_2770_; lean_object* v_powFn_x3f_2771_; 
v_toRing_2770_ = lean_ctor_get(v_a_2766_, 0);
lean_inc_ref(v_toRing_2770_);
lean_dec(v_a_2766_);
v_powFn_x3f_2771_ = lean_ctor_get(v_toRing_2770_, 10);
if (lean_obj_tag(v_powFn_x3f_2771_) == 1)
{
lean_object* v_val_2772_; lean_object* v___x_2774_; 
lean_inc_ref(v_powFn_x3f_2771_);
lean_dec_ref(v_toRing_2770_);
v_val_2772_ = lean_ctor_get(v_powFn_x3f_2771_, 0);
lean_inc(v_val_2772_);
lean_dec_ref(v_powFn_x3f_2771_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v_val_2772_);
v___x_2774_ = v___x_2768_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_val_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
else
{
lean_object* v_type_2776_; lean_object* v_u_2777_; lean_object* v_semiringInst_2778_; lean_object* v___x_2779_; 
lean_del_object(v___x_2768_);
v_type_2776_ = lean_ctor_get(v_toRing_2770_, 1);
lean_inc_ref(v_type_2776_);
v_u_2777_ = lean_ctor_get(v_toRing_2770_, 2);
lean_inc(v_u_2777_);
v_semiringInst_2778_ = lean_ctor_get(v_toRing_2770_, 4);
lean_inc_ref(v_semiringInst_2778_);
lean_dec_ref(v_toRing_2770_);
v___x_2779_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2777_, v_type_2776_, v_semiringInst_2778_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___f_2781_; lean_object* v___x_2782_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref(v___x_2779_);
lean_inc(v_a_2780_);
v___f_2781_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_2781_, 0, v_a_2780_);
v___x_2782_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2781_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v___x_2782_, 0);
lean_dec(v_unused_2790_);
v___x_2784_ = v___x_2782_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_dec(v___x_2782_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v_a_2780_);
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2780_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v_a_2780_);
v_a_2791_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2782_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2782_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
else
{
return v___x_2779_;
}
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
v_a_2800_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2765_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2765_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec(v___y_2808_);
return v_res_2820_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2));
v___x_2825_ = lean_unsigned_to_nat(39u);
v___x_2826_ = lean_unsigned_to_nat(158u);
v___x_2827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1));
v___x_2828_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0));
v___x_2829_ = l_mkPanicMessageWithDecl(v___x_2828_, v___x_2827_, v___x_2826_, v___x_2825_, v___x_2824_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
switch(lean_obj_tag(v_a_2830_))
{
case 0:
{
lean_object* v_k_2843_; lean_object* v___x_2844_; 
v_k_2843_ = lean_ctor_get(v_a_2830_, 0);
lean_inc(v_k_2843_);
lean_dec_ref(v_a_2830_);
v___x_2844_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2843_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
lean_dec(v_k_2843_);
return v___x_2844_;
}
case 1:
{
lean_object* v_k_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_k_2845_ = lean_ctor_get(v_a_2830_, 0);
lean_inc(v_k_2845_);
lean_dec_ref(v_a_2830_);
v___x_2846_ = lean_nat_to_int(v_k_2845_);
v___x_2847_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v___x_2846_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
lean_dec(v___x_2846_);
return v___x_2847_;
}
case 3:
{
lean_object* v_i_2848_; lean_object* v___x_2849_; 
v_i_2848_ = lean_ctor_get(v_a_2830_, 0);
lean_inc(v_i_2848_);
lean_dec_ref(v_a_2830_);
v___x_2849_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___x_2849_);
v___x_2851_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2869_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2854_ = v___x_2851_;
v_isShared_2855_ = v_isSharedCheck_2869_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2851_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2869_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___y_2857_; lean_object* v_toSemiring_2862_; lean_object* v_vars_2863_; lean_object* v_size_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; 
v_toSemiring_2862_ = lean_ctor_get(v_a_2852_, 0);
lean_inc_ref(v_toSemiring_2862_);
lean_dec(v_a_2852_);
v_vars_2863_ = lean_ctor_get(v_toSemiring_2862_, 9);
lean_inc_ref(v_vars_2863_);
lean_dec_ref(v_toSemiring_2862_);
v_size_2864_ = lean_ctor_get(v_vars_2863_, 2);
v___x_2865_ = l_Lean_instInhabitedExpr;
v___x_2866_ = lean_nat_dec_lt(v_i_2848_, v_size_2864_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; 
lean_dec_ref(v_vars_2863_);
lean_dec(v_i_2848_);
v___x_2867_ = l_outOfBounds___redArg(v___x_2865_);
v___y_2857_ = v___x_2867_;
goto v___jp_2856_;
}
else
{
lean_object* v___x_2868_; 
v___x_2868_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2865_, v_vars_2863_, v_i_2848_);
lean_dec(v_i_2848_);
v___y_2857_ = v___x_2868_;
goto v___jp_2856_;
}
v___jp_2856_:
{
lean_object* v___x_2858_; lean_object* v___x_2860_; 
v___x_2858_ = l_Lean_Expr_app___override(v_a_2850_, v___y_2857_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v___x_2858_);
v___x_2860_ = v___x_2854_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec(v_a_2850_);
lean_dec(v_i_2848_);
v_a_2870_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2851_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2851_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
else
{
lean_dec(v_i_2848_);
return v___x_2849_;
}
}
case 5:
{
lean_object* v_a_2878_; lean_object* v_b_2879_; lean_object* v___x_2880_; 
v_a_2878_ = lean_ctor_get(v_a_2830_, 0);
lean_inc_ref(v_a_2878_);
v_b_2879_ = lean_ctor_get(v_a_2830_, 1);
lean_inc_ref(v_b_2879_);
lean_dec_ref(v_a_2830_);
v___x_2880_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2882_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref(v___x_2880_);
v___x_2882_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2878_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2882_);
v___x_2884_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2879_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2893_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2887_ = v___x_2884_;
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2889_ = l_Lean_mkAppB(v_a_2881_, v_a_2883_, v_a_2885_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2889_);
v___x_2891_ = v___x_2887_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
else
{
lean_dec(v_a_2883_);
lean_dec(v_a_2881_);
return v___x_2884_;
}
}
else
{
lean_dec(v_a_2881_);
lean_dec_ref(v_b_2879_);
return v___x_2882_;
}
}
else
{
lean_dec_ref(v_b_2879_);
lean_dec_ref(v_a_2878_);
return v___x_2880_;
}
}
case 7:
{
lean_object* v_a_2894_; lean_object* v_b_2895_; lean_object* v___x_2896_; 
v_a_2894_ = lean_ctor_get(v_a_2830_, 0);
lean_inc_ref(v_a_2894_);
v_b_2895_ = lean_ctor_get(v_a_2830_, 1);
lean_inc_ref(v_b_2895_);
lean_dec_ref(v_a_2830_);
v___x_2896_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref(v___x_2896_);
v___x_2898_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2894_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2900_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref(v___x_2898_);
v___x_2900_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2895_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2909_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2903_ = v___x_2900_;
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2909_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2905_ = l_Lean_mkAppB(v_a_2897_, v_a_2899_, v_a_2901_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2905_);
v___x_2907_ = v___x_2903_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
else
{
lean_dec(v_a_2899_);
lean_dec(v_a_2897_);
return v___x_2900_;
}
}
else
{
lean_dec(v_a_2897_);
lean_dec_ref(v_b_2895_);
return v___x_2898_;
}
}
else
{
lean_dec_ref(v_b_2895_);
lean_dec_ref(v_a_2894_);
return v___x_2896_;
}
}
case 8:
{
lean_object* v_a_2910_; lean_object* v_k_2911_; lean_object* v___x_2912_; 
v_a_2910_ = lean_ctor_get(v_a_2830_, 0);
lean_inc_ref(v_a_2910_);
v_k_2911_ = lean_ctor_get(v_a_2830_, 1);
lean_inc(v_k_2911_);
lean_dec_ref(v_a_2830_);
v___x_2912_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2914_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref(v___x_2912_);
v___x_2914_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2910_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2924_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2917_ = v___x_2914_;
v_isShared_2918_ = v_isSharedCheck_2924_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2914_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2924_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2919_ = l_Lean_mkNatLit(v_k_2911_);
v___x_2920_ = l_Lean_mkAppB(v_a_2913_, v_a_2915_, v___x_2919_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v___x_2920_);
v___x_2922_ = v___x_2917_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
else
{
lean_dec(v_a_2913_);
lean_dec(v_k_2911_);
return v___x_2914_;
}
}
else
{
lean_dec(v_k_2911_);
lean_dec_ref(v_a_2910_);
return v___x_2912_;
}
}
default: 
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_dec_ref(v_a_2830_);
v___x_2925_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3);
v___x_2926_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___x_2925_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
return v___x_2926_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
lean_dec(v_a_2932_);
lean_dec_ref(v_a_2931_);
lean_dec(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec(v_a_2928_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(lean_object* v_type_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_2941_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___boxed(lean_object* v_type_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(v_type_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec(v___y_2956_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object* v_e_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_e_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2984_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref(v___x_2982_);
v___x_2984_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2983_, v_a_2976_);
return v___x_2984_;
}
else
{
return v___x_2982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object* v_e_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(v_e_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec(v_a_2987_);
lean_dec(v_a_2986_);
return v_res_2998_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM);
l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
}
#ifdef __cplusplus
}
#endif
