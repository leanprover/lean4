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
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "expression in two different semirings"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "failed to find instance"};
static const lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_104_ = l_Lean_Meta_Sym_canon(v_e_91_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
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
v___x_134_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_e_121_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
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
v___x_654_ = l_Lean_Meta_Sym_canon(v___x_653_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
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
lean_inc_n(v_a_615_, 2);
lean_dec_ref(v___y_614_);
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
v___x_699_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_add_698_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
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
v___x_708_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_707_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
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
lean_inc_n(v_a_835_, 2);
lean_dec_ref(v___x_834_);
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
lean_inc_ref_n(v_type_938_, 3);
v_u_939_ = lean_ctor_get(v_s_934_, 2);
lean_inc_n(v_u_939_, 2);
v_semiringInst_940_ = lean_ctor_get(v_s_934_, 3);
lean_inc_ref(v_semiringInst_940_);
lean_dec_ref(v_s_934_);
v___x_941_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_942_ = lean_box(0);
v___x_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_943_, 0, v_u_939_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
lean_inc_ref(v___x_943_);
v___x_944_ = l_Lean_mkConst(v___x_941_, v___x_943_);
v___x_945_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_946_ = l_Lean_mkConst(v___x_945_, v___x_943_);
v___x_947_ = l_Lean_mkAppB(v___x_946_, v_type_938_, v_semiringInst_940_);
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
lean_inc_n(v_toBind_959_, 3);
v_getSemiring_960_ = lean_ctor_get(v_inst_957_, 0);
lean_inc(v_getSemiring_960_);
v_modifySemiring_961_ = lean_ctor_get(v_inst_957_, 1);
lean_inc(v_modifySemiring_961_);
lean_dec_ref(v_inst_957_);
v_toPure_962_ = lean_ctor_get(v_toApplicative_958_, 1);
lean_inc_n(v_toPure_962_, 2);
v___f_963_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_963_, 0, v_toPure_962_);
lean_closure_set(v___f_963_, 1, v_modifySemiring_961_);
lean_closure_set(v___f_963_, 2, v_toBind_959_);
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
lean_inc_ref_n(v_type_1033_, 3);
v_u_1034_ = lean_ctor_get(v_s_1029_, 2);
lean_inc_n(v_u_1034_, 2);
v_semiringInst_1035_ = lean_ctor_get(v_s_1029_, 3);
lean_inc_ref(v_semiringInst_1035_);
lean_dec_ref(v_s_1029_);
v___x_1036_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_1037_ = lean_box(0);
v___x_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1038_, 0, v_u_1034_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
lean_inc_ref(v___x_1038_);
v___x_1039_ = l_Lean_mkConst(v___x_1036_, v___x_1038_);
v___x_1040_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_1041_ = l_Lean_mkConst(v___x_1040_, v___x_1038_);
v___x_1042_ = l_Lean_mkAppB(v___x_1041_, v_type_1033_, v_semiringInst_1035_);
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
lean_inc_n(v_toBind_1054_, 3);
v_getSemiring_1055_ = lean_ctor_get(v_inst_1052_, 0);
lean_inc(v_getSemiring_1055_);
v_modifySemiring_1056_ = lean_ctor_get(v_inst_1052_, 1);
lean_inc(v_modifySemiring_1056_);
lean_dec_ref(v_inst_1052_);
v_toPure_1057_ = lean_ctor_get(v_toApplicative_1053_, 1);
lean_inc_n(v_toPure_1057_, 2);
v___f_1058_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1058_, 0, v_toPure_1057_);
lean_closure_set(v___f_1058_, 1, v_modifySemiring_1056_);
lean_closure_set(v___f_1058_, 2, v_toBind_1054_);
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
lean_inc_n(v_toBind_1123_, 3);
v_getSemiring_1124_ = lean_ctor_get(v_inst_1121_, 0);
lean_inc(v_getSemiring_1124_);
v_modifySemiring_1125_ = lean_ctor_get(v_inst_1121_, 1);
lean_inc(v_modifySemiring_1125_);
lean_dec_ref(v_inst_1121_);
v_toPure_1126_ = lean_ctor_get(v_toApplicative_1122_, 1);
lean_inc_n(v_toPure_1126_, 2);
v___f_1127_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1127_, 0, v_toPure_1126_);
lean_closure_set(v___f_1127_, 1, v_modifySemiring_1125_);
lean_closure_set(v___f_1127_, 2, v_toBind_1123_);
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
lean_inc_n(v_toBind_1190_, 3);
v_getSemiring_1191_ = lean_ctor_get(v_inst_1188_, 0);
lean_inc(v_getSemiring_1191_);
v_modifySemiring_1192_ = lean_ctor_get(v_inst_1188_, 1);
lean_inc(v_modifySemiring_1192_);
lean_dec_ref(v_inst_1188_);
v_toPure_1193_ = lean_ctor_get(v_toApplicative_1189_, 1);
lean_inc_n(v_toPure_1193_, 2);
v___f_1194_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1194_, 0, v_toPure_1193_);
lean_closure_set(v___f_1194_, 1, v_modifySemiring_1192_);
lean_closure_set(v___f_1194_, 2, v_toBind_1190_);
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
size_t v_x_7254__boxed_1498_; size_t v_x_7255__boxed_1499_; lean_object* v_res_1500_; 
v_x_7254__boxed_1498_ = lean_unbox_usize(v_x_1494_);
lean_dec(v_x_1494_);
v_x_7255__boxed_1499_ = lean_unbox_usize(v_x_1495_);
lean_dec(v_x_1495_);
v_res_1500_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1493_, v_x_7254__boxed_1498_, v_x_7255__boxed_1499_, v_x_1496_, v_x_1497_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(lean_object* v_e_1508_, lean_object* v_a_1509_, lean_object* v_s_1510_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(lean_object* v_e_1532_, lean_object* v_a_1533_, lean_object* v_s_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(v_e_1532_, v_a_1533_, v_s_1534_);
lean_dec(v_a_1533_);
return v_res_1535_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0));
v___x_1538_ = l_Lean_stringToMessageData(v___x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object* v_e_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1539_, v_a_1541_, v_a_1546_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
if (lean_obj_tag(v_a_1553_) == 1)
{
lean_object* v_val_1554_; uint8_t v___x_1555_; 
v_val_1554_ = lean_ctor_get(v_a_1553_, 0);
lean_inc(v_val_1554_);
lean_dec_ref(v_a_1553_);
v___x_1555_ = lean_nat_dec_eq(v_val_1554_, v_a_1540_);
lean_dec(v_val_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1542_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; uint8_t v___x_1558_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref(v___x_1556_);
v___x_1558_ = lean_unbox(v_a_1557_);
lean_dec(v_a_1557_);
if (v___x_1558_ == 0)
{
lean_dec_ref(v_e_1539_);
goto v___jp_1549_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1559_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1);
v___x_1560_ = l_Lean_indentExpr(v_e_1539_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = l_Lean_Meta_Sym_reportIssue(v___x_1561_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_dec_ref(v___x_1562_);
goto v___jp_1549_;
}
else
{
return v___x_1562_;
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec_ref(v_e_1539_);
v_a_1563_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1556_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1556_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_dec_ref(v_e_1539_);
goto v___jp_1549_;
}
}
else
{
lean_object* v___f_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
lean_dec(v_a_1553_);
lean_inc(v_a_1540_);
v___f_1571_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1571_, 0, v_e_1539_);
lean_closure_set(v___f_1571_, 1, v_a_1540_);
v___x_1572_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1573_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1572_, v___f_1571_, v_a_1541_);
return v___x_1573_;
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v_e_1539_);
v_a_1574_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1552_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1552_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
v___jp_1549_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_box(0);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
return v___x_1551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(lean_object* v_e_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec_ref(v_a_1587_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
lean_dec(v_a_1584_);
lean_dec(v_a_1583_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object* v_e_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1593_, v_a_1594_, v_a_1595_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object* v_e_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec(v_a_1608_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object* v_00_u03b2_1621_, lean_object* v_x_1622_, lean_object* v_x_1623_, lean_object* v_x_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_x_1622_, v_x_1623_, v_x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_1626_, lean_object* v_x_1627_, size_t v_x_1628_, size_t v_x_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1627_, v_x_1628_, v_x_1629_, v_x_1630_, v_x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_){
_start:
{
size_t v_x_7533__boxed_1639_; size_t v_x_7534__boxed_1640_; lean_object* v_res_1641_; 
v_x_7533__boxed_1639_ = lean_unbox_usize(v_x_1635_);
lean_dec(v_x_1635_);
v_x_7534__boxed_1640_ = lean_unbox_usize(v_x_1636_);
lean_dec(v_x_1636_);
v_res_1641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(v_00_u03b2_1633_, v_x_1634_, v_x_7533__boxed_1639_, v_x_7534__boxed_1640_, v_x_1637_, v_x_1638_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1642_, lean_object* v_n_1643_, lean_object* v_k_1644_, lean_object* v_v_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v_n_1643_, v_k_1644_, v_v_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1647_, size_t v_depth_1648_, lean_object* v_keys_1649_, lean_object* v_vals_1650_, lean_object* v_heq_1651_, lean_object* v_i_1652_, lean_object* v_entries_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_1648_, v_keys_1649_, v_vals_1650_, v_i_1652_, v_entries_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1655_, lean_object* v_depth_1656_, lean_object* v_keys_1657_, lean_object* v_vals_1658_, lean_object* v_heq_1659_, lean_object* v_i_1660_, lean_object* v_entries_1661_){
_start:
{
size_t v_depth_boxed_1662_; lean_object* v_res_1663_; 
v_depth_boxed_1662_ = lean_unbox_usize(v_depth_1656_);
lean_dec(v_depth_1656_);
v_res_1663_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_1655_, v_depth_boxed_1662_, v_keys_1657_, v_vals_1658_, v_heq_1659_, v_i_1660_, v_entries_1661_);
lean_dec_ref(v_vals_1658_);
lean_dec_ref(v_keys_1657_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1665_, v_x_1666_, v_x_1667_, v_x_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(lean_object* v_e_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1670_, v___y_1671_, v___y_1672_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(lean_object* v_e_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(v_e_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec(v___y_1685_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object* v_e_1700_, lean_object* v___f_1701_, lean_object* v___f_1702_, lean_object* v_size_1703_, lean_object* v_s_1704_){
_start:
{
lean_object* v_id_1705_; lean_object* v_type_1706_; lean_object* v_u_1707_; lean_object* v_semiringInst_1708_; lean_object* v_addFn_x3f_1709_; lean_object* v_mulFn_x3f_1710_; lean_object* v_powFn_x3f_1711_; lean_object* v_natCastFn_x3f_1712_; lean_object* v_denote_1713_; lean_object* v_vars_1714_; lean_object* v_varMap_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1724_; 
v_id_1705_ = lean_ctor_get(v_s_1704_, 0);
v_type_1706_ = lean_ctor_get(v_s_1704_, 1);
v_u_1707_ = lean_ctor_get(v_s_1704_, 2);
v_semiringInst_1708_ = lean_ctor_get(v_s_1704_, 3);
v_addFn_x3f_1709_ = lean_ctor_get(v_s_1704_, 4);
v_mulFn_x3f_1710_ = lean_ctor_get(v_s_1704_, 5);
v_powFn_x3f_1711_ = lean_ctor_get(v_s_1704_, 6);
v_natCastFn_x3f_1712_ = lean_ctor_get(v_s_1704_, 7);
v_denote_1713_ = lean_ctor_get(v_s_1704_, 8);
v_vars_1714_ = lean_ctor_get(v_s_1704_, 9);
v_varMap_1715_ = lean_ctor_get(v_s_1704_, 10);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_s_1704_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1717_ = v_s_1704_;
v_isShared_1718_ = v_isSharedCheck_1724_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_varMap_1715_);
lean_inc(v_vars_1714_);
lean_inc(v_denote_1713_);
lean_inc(v_natCastFn_x3f_1712_);
lean_inc(v_powFn_x3f_1711_);
lean_inc(v_mulFn_x3f_1710_);
lean_inc(v_addFn_x3f_1709_);
lean_inc(v_semiringInst_1708_);
lean_inc(v_u_1707_);
lean_inc(v_type_1706_);
lean_inc(v_id_1705_);
lean_dec(v_s_1704_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1724_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
lean_inc_ref(v_e_1700_);
v___x_1719_ = l_Lean_PersistentArray_push___redArg(v_vars_1714_, v_e_1700_);
v___x_1720_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1701_, v___f_1702_, v_varMap_1715_, v_e_1700_, v_size_1703_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 10, v___x_1720_);
lean_ctor_set(v___x_1717_, 9, v___x_1719_);
v___x_1722_ = v___x_1717_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_id_1705_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_type_1706_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_u_1707_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v_semiringInst_1708_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v_addFn_x3f_1709_);
lean_ctor_set(v_reuseFailAlloc_1723_, 5, v_mulFn_x3f_1710_);
lean_ctor_set(v_reuseFailAlloc_1723_, 6, v_powFn_x3f_1711_);
lean_ctor_set(v_reuseFailAlloc_1723_, 7, v_natCastFn_x3f_1712_);
lean_ctor_set(v_reuseFailAlloc_1723_, 8, v_denote_1713_);
lean_ctor_set(v_reuseFailAlloc_1723_, 9, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1723_, 10, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object* v_toPure_1725_, lean_object* v_size_1726_, lean_object* v_____r_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_apply_2(v_toPure_1725_, lean_box(0), v_size_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object* v_e_1729_, lean_object* v_inst_1730_, lean_object* v_toBind_1731_, lean_object* v___f_1732_, lean_object* v_____r_1733_){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1734_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1735_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_1735_, 0, lean_box(0));
lean_closure_set(v___x_1735_, 1, v___x_1734_);
lean_closure_set(v___x_1735_, 2, v_e_1729_);
v___x_1736_ = lean_apply_2(v_inst_1730_, lean_box(0), v___x_1735_);
v___x_1737_ = lean_apply_4(v_toBind_1731_, lean_box(0), lean_box(0), v___x_1736_, v___f_1732_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object* v_inst_1738_, lean_object* v_e_1739_, lean_object* v_toBind_1740_, lean_object* v___f_1741_, lean_object* v_____r_1742_){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_apply_1(v_inst_1738_, v_e_1739_);
v___x_1744_ = lean_apply_4(v_toBind_1740_, lean_box(0), lean_box(0), v___x_1743_, v___f_1741_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object* v___f_1745_, lean_object* v___f_1746_, lean_object* v_e_1747_, lean_object* v_toPure_1748_, lean_object* v_inst_1749_, lean_object* v_toBind_1750_, lean_object* v_inst_1751_, lean_object* v_modifySemiring_1752_, lean_object* v_s_1753_){
_start:
{
lean_object* v_vars_1754_; lean_object* v_varMap_1755_; lean_object* v___x_1756_; 
v_vars_1754_ = lean_ctor_get(v_s_1753_, 9);
lean_inc_ref(v_vars_1754_);
v_varMap_1755_ = lean_ctor_get(v_s_1753_, 10);
lean_inc_ref(v_varMap_1755_);
lean_dec_ref(v_s_1753_);
lean_inc_ref(v_e_1747_);
lean_inc_ref(v___f_1746_);
lean_inc_ref(v___f_1745_);
v___x_1756_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_1745_, v___f_1746_, v_varMap_1755_, v_e_1747_);
if (lean_obj_tag(v___x_1756_) == 1)
{
lean_object* v_val_1757_; lean_object* v___x_1758_; 
lean_dec_ref(v_vars_1754_);
lean_dec(v_modifySemiring_1752_);
lean_dec(v_inst_1751_);
lean_dec(v_toBind_1750_);
lean_dec(v_inst_1749_);
lean_dec_ref(v_e_1747_);
lean_dec_ref(v___f_1746_);
lean_dec_ref(v___f_1745_);
v_val_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_val_1757_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = lean_apply_2(v_toPure_1748_, lean_box(0), v_val_1757_);
return v___x_1758_;
}
else
{
lean_object* v_size_1759_; lean_object* v___f_1760_; lean_object* v___f_1761_; lean_object* v___f_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec(v___x_1756_);
v_size_1759_ = lean_ctor_get(v_vars_1754_, 2);
lean_inc_n(v_size_1759_, 2);
lean_dec_ref(v_vars_1754_);
lean_inc_ref_n(v_e_1747_, 2);
v___f_1760_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1760_, 0, v_e_1747_);
lean_closure_set(v___f_1760_, 1, v___f_1745_);
lean_closure_set(v___f_1760_, 2, v___f_1746_);
lean_closure_set(v___f_1760_, 3, v_size_1759_);
v___f_1761_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1761_, 0, v_toPure_1748_);
lean_closure_set(v___f_1761_, 1, v_size_1759_);
lean_inc_n(v_toBind_1750_, 2);
v___f_1762_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1762_, 0, v_e_1747_);
lean_closure_set(v___f_1762_, 1, v_inst_1749_);
lean_closure_set(v___f_1762_, 2, v_toBind_1750_);
lean_closure_set(v___f_1762_, 3, v___f_1761_);
v___f_1763_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1763_, 0, v_inst_1751_);
lean_closure_set(v___f_1763_, 1, v_e_1747_);
lean_closure_set(v___f_1763_, 2, v_toBind_1750_);
lean_closure_set(v___f_1763_, 3, v___f_1762_);
v___x_1764_ = lean_apply_1(v_modifySemiring_1752_, v___f_1760_);
v___x_1765_ = lean_apply_4(v_toBind_1750_, lean_box(0), lean_box(0), v___x_1764_, v___f_1763_);
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object* v_inst_1768_, lean_object* v_inst_1769_, lean_object* v_inst_1770_, lean_object* v_inst_1771_, lean_object* v_e_1772_){
_start:
{
lean_object* v_toApplicative_1773_; lean_object* v_toBind_1774_; lean_object* v_getSemiring_1775_; lean_object* v_modifySemiring_1776_; lean_object* v_toPure_1777_; lean_object* v___f_1778_; lean_object* v___f_1779_; lean_object* v___f_1780_; lean_object* v___x_1781_; 
v_toApplicative_1773_ = lean_ctor_get(v_inst_1769_, 0);
lean_inc_ref(v_toApplicative_1773_);
v_toBind_1774_ = lean_ctor_get(v_inst_1769_, 1);
lean_inc_n(v_toBind_1774_, 2);
lean_dec_ref(v_inst_1769_);
v_getSemiring_1775_ = lean_ctor_get(v_inst_1770_, 0);
lean_inc(v_getSemiring_1775_);
v_modifySemiring_1776_ = lean_ctor_get(v_inst_1770_, 1);
lean_inc(v_modifySemiring_1776_);
lean_dec_ref(v_inst_1770_);
v_toPure_1777_ = lean_ctor_get(v_toApplicative_1773_, 1);
lean_inc(v_toPure_1777_);
lean_dec_ref(v_toApplicative_1773_);
v___f_1778_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0));
v___f_1779_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1));
v___f_1780_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1780_, 0, v___f_1778_);
lean_closure_set(v___f_1780_, 1, v___f_1779_);
lean_closure_set(v___f_1780_, 2, v_e_1772_);
lean_closure_set(v___f_1780_, 3, v_toPure_1777_);
lean_closure_set(v___f_1780_, 4, v_inst_1768_);
lean_closure_set(v___f_1780_, 5, v_toBind_1774_);
lean_closure_set(v___f_1780_, 6, v_inst_1771_);
lean_closure_set(v___f_1780_, 7, v_modifySemiring_1776_);
v___x_1781_ = lean_apply_4(v_toBind_1774_, lean_box(0), lean_box(0), v_getSemiring_1775_, v___f_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object* v_m_1782_, lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_e_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v_inst_1783_, v_inst_1784_, v_inst_1785_, v_inst_1786_, v_e_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(lean_object* v___y_1789_, lean_object* v_e_1790_, lean_object* v_size_1791_, lean_object* v_s_1792_){
_start:
{
lean_object* v_rings_1793_; lean_object* v_typeIdOf_1794_; lean_object* v_exprToRingId_1795_; lean_object* v_semirings_1796_; lean_object* v_stypeIdOf_1797_; lean_object* v_exprToSemiringId_1798_; lean_object* v_ncRings_1799_; lean_object* v_exprToNCRingId_1800_; lean_object* v_nctypeIdOf_1801_; lean_object* v_ncSemirings_1802_; lean_object* v_exprToNCSemiringId_1803_; lean_object* v_ncstypeIdOf_1804_; lean_object* v_steps_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_rings_1793_ = lean_ctor_get(v_s_1792_, 0);
v_typeIdOf_1794_ = lean_ctor_get(v_s_1792_, 1);
v_exprToRingId_1795_ = lean_ctor_get(v_s_1792_, 2);
v_semirings_1796_ = lean_ctor_get(v_s_1792_, 3);
v_stypeIdOf_1797_ = lean_ctor_get(v_s_1792_, 4);
v_exprToSemiringId_1798_ = lean_ctor_get(v_s_1792_, 5);
v_ncRings_1799_ = lean_ctor_get(v_s_1792_, 6);
v_exprToNCRingId_1800_ = lean_ctor_get(v_s_1792_, 7);
v_nctypeIdOf_1801_ = lean_ctor_get(v_s_1792_, 8);
v_ncSemirings_1802_ = lean_ctor_get(v_s_1792_, 9);
v_exprToNCSemiringId_1803_ = lean_ctor_get(v_s_1792_, 10);
v_ncstypeIdOf_1804_ = lean_ctor_get(v_s_1792_, 11);
v_steps_1805_ = lean_ctor_get(v_s_1792_, 12);
v___x_1806_ = lean_array_get_size(v_semirings_1796_);
v___x_1807_ = lean_nat_dec_lt(v___y_1789_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_dec(v_size_1791_);
lean_dec_ref(v_e_1790_);
return v_s_1792_;
}
else
{
lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1850_; 
lean_inc(v_steps_1805_);
lean_inc_ref(v_ncstypeIdOf_1804_);
lean_inc_ref(v_exprToNCSemiringId_1803_);
lean_inc_ref(v_ncSemirings_1802_);
lean_inc_ref(v_nctypeIdOf_1801_);
lean_inc_ref(v_exprToNCRingId_1800_);
lean_inc_ref(v_ncRings_1799_);
lean_inc_ref(v_exprToSemiringId_1798_);
lean_inc_ref(v_stypeIdOf_1797_);
lean_inc_ref(v_semirings_1796_);
lean_inc_ref(v_exprToRingId_1795_);
lean_inc_ref(v_typeIdOf_1794_);
lean_inc_ref(v_rings_1793_);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_s_1792_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; lean_object* v_unused_1860_; lean_object* v_unused_1861_; lean_object* v_unused_1862_; lean_object* v_unused_1863_; 
v_unused_1851_ = lean_ctor_get(v_s_1792_, 12);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_s_1792_, 11);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v_s_1792_, 10);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_s_1792_, 9);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v_s_1792_, 8);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_s_1792_, 7);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_s_1792_, 6);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_s_1792_, 5);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_s_1792_, 4);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v_s_1792_, 3);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v_s_1792_, 2);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v_s_1792_, 1);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v_s_1792_, 0);
lean_dec(v_unused_1863_);
v___x_1809_ = v_s_1792_;
v_isShared_1810_ = v_isSharedCheck_1850_;
goto v_resetjp_1808_;
}
else
{
lean_dec(v_s_1792_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1850_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v_v_1811_; lean_object* v_toSemiring_1812_; lean_object* v_ringId_1813_; lean_object* v_commSemiringInst_1814_; lean_object* v_addRightCancelInst_x3f_1815_; lean_object* v_toQFn_x3f_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1849_; 
v_v_1811_ = lean_array_fget(v_semirings_1796_, v___y_1789_);
v_toSemiring_1812_ = lean_ctor_get(v_v_1811_, 0);
v_ringId_1813_ = lean_ctor_get(v_v_1811_, 1);
v_commSemiringInst_1814_ = lean_ctor_get(v_v_1811_, 2);
v_addRightCancelInst_x3f_1815_ = lean_ctor_get(v_v_1811_, 3);
v_toQFn_x3f_1816_ = lean_ctor_get(v_v_1811_, 4);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_v_1811_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1818_ = v_v_1811_;
v_isShared_1819_ = v_isSharedCheck_1849_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_toQFn_x3f_1816_);
lean_inc(v_addRightCancelInst_x3f_1815_);
lean_inc(v_commSemiringInst_1814_);
lean_inc(v_ringId_1813_);
lean_inc(v_toSemiring_1812_);
lean_dec(v_v_1811_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1849_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_id_1820_; lean_object* v_type_1821_; lean_object* v_u_1822_; lean_object* v_semiringInst_1823_; lean_object* v_addFn_x3f_1824_; lean_object* v_mulFn_x3f_1825_; lean_object* v_powFn_x3f_1826_; lean_object* v_natCastFn_x3f_1827_; lean_object* v_denote_1828_; lean_object* v_vars_1829_; lean_object* v_varMap_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1848_; 
v_id_1820_ = lean_ctor_get(v_toSemiring_1812_, 0);
v_type_1821_ = lean_ctor_get(v_toSemiring_1812_, 1);
v_u_1822_ = lean_ctor_get(v_toSemiring_1812_, 2);
v_semiringInst_1823_ = lean_ctor_get(v_toSemiring_1812_, 3);
v_addFn_x3f_1824_ = lean_ctor_get(v_toSemiring_1812_, 4);
v_mulFn_x3f_1825_ = lean_ctor_get(v_toSemiring_1812_, 5);
v_powFn_x3f_1826_ = lean_ctor_get(v_toSemiring_1812_, 6);
v_natCastFn_x3f_1827_ = lean_ctor_get(v_toSemiring_1812_, 7);
v_denote_1828_ = lean_ctor_get(v_toSemiring_1812_, 8);
v_vars_1829_ = lean_ctor_get(v_toSemiring_1812_, 9);
v_varMap_1830_ = lean_ctor_get(v_toSemiring_1812_, 10);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_toSemiring_1812_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1832_ = v_toSemiring_1812_;
v_isShared_1833_ = v_isSharedCheck_1848_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_varMap_1830_);
lean_inc(v_vars_1829_);
lean_inc(v_denote_1828_);
lean_inc(v_natCastFn_x3f_1827_);
lean_inc(v_powFn_x3f_1826_);
lean_inc(v_mulFn_x3f_1825_);
lean_inc(v_addFn_x3f_1824_);
lean_inc(v_semiringInst_1823_);
lean_inc(v_u_1822_);
lean_inc(v_type_1821_);
lean_inc(v_id_1820_);
lean_dec(v_toSemiring_1812_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1848_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v_xs_x27_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1834_ = lean_box(0);
v_xs_x27_1835_ = lean_array_fset(v_semirings_1796_, v___y_1789_, v___x_1834_);
lean_inc_ref(v_e_1790_);
v___x_1836_ = l_Lean_PersistentArray_push___redArg(v_vars_1829_, v_e_1790_);
v___x_1837_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_varMap_1830_, v_e_1790_, v_size_1791_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 10, v___x_1837_);
lean_ctor_set(v___x_1832_, 9, v___x_1836_);
v___x_1839_ = v___x_1832_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_id_1820_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_type_1821_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_u_1822_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_semiringInst_1823_);
lean_ctor_set(v_reuseFailAlloc_1847_, 4, v_addFn_x3f_1824_);
lean_ctor_set(v_reuseFailAlloc_1847_, 5, v_mulFn_x3f_1825_);
lean_ctor_set(v_reuseFailAlloc_1847_, 6, v_powFn_x3f_1826_);
lean_ctor_set(v_reuseFailAlloc_1847_, 7, v_natCastFn_x3f_1827_);
lean_ctor_set(v_reuseFailAlloc_1847_, 8, v_denote_1828_);
lean_ctor_set(v_reuseFailAlloc_1847_, 9, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1847_, 10, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1839_);
v___x_1841_ = v___x_1818_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_ringId_1813_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_commSemiringInst_1814_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_addRightCancelInst_x3f_1815_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v_toQFn_x3f_1816_);
v___x_1841_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_array_fset(v_xs_x27_1835_, v___y_1789_, v___x_1841_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 3, v___x_1842_);
v___x_1844_ = v___x_1809_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_rings_1793_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_typeIdOf_1794_);
lean_ctor_set(v_reuseFailAlloc_1845_, 2, v_exprToRingId_1795_);
lean_ctor_set(v_reuseFailAlloc_1845_, 3, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1845_, 4, v_stypeIdOf_1797_);
lean_ctor_set(v_reuseFailAlloc_1845_, 5, v_exprToSemiringId_1798_);
lean_ctor_set(v_reuseFailAlloc_1845_, 6, v_ncRings_1799_);
lean_ctor_set(v_reuseFailAlloc_1845_, 7, v_exprToNCRingId_1800_);
lean_ctor_set(v_reuseFailAlloc_1845_, 8, v_nctypeIdOf_1801_);
lean_ctor_set(v_reuseFailAlloc_1845_, 9, v_ncSemirings_1802_);
lean_ctor_set(v_reuseFailAlloc_1845_, 10, v_exprToNCSemiringId_1803_);
lean_ctor_set(v_reuseFailAlloc_1845_, 11, v_ncstypeIdOf_1804_);
lean_ctor_set(v_reuseFailAlloc_1845_, 12, v_steps_1805_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed(lean_object* v___y_1864_, lean_object* v_e_1865_, lean_object* v_size_1866_, lean_object* v_s_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(v___y_1864_, v_e_1865_, v_size_1866_, v_s_1867_);
lean_dec(v___y_1864_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(lean_object* v_e_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1933_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1933_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1933_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_toSemiring_1887_; lean_object* v_vars_1888_; lean_object* v_varMap_1889_; lean_object* v___x_1890_; 
v_toSemiring_1887_ = lean_ctor_get(v_a_1883_, 0);
lean_inc_ref(v_toSemiring_1887_);
lean_dec(v_a_1883_);
v_vars_1888_ = lean_ctor_get(v_toSemiring_1887_, 9);
lean_inc_ref(v_vars_1888_);
v_varMap_1889_ = lean_ctor_get(v_toSemiring_1887_, 10);
lean_inc_ref(v_varMap_1889_);
lean_dec_ref(v_toSemiring_1887_);
v___x_1890_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_varMap_1889_, v_e_1869_);
if (lean_obj_tag(v___x_1890_) == 1)
{
lean_object* v_val_1891_; lean_object* v___x_1893_; 
lean_dec_ref(v_vars_1888_);
lean_dec_ref(v_e_1869_);
v_val_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_val_1891_);
lean_dec_ref(v___x_1890_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v_val_1891_);
v___x_1893_ = v___x_1885_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_val_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
else
{
lean_object* v_size_1895_; lean_object* v___f_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec(v___x_1890_);
lean_del_object(v___x_1885_);
v_size_1895_ = lean_ctor_get(v_vars_1888_, 2);
lean_inc_n(v_size_1895_, 2);
lean_dec_ref(v_vars_1888_);
lean_inc_ref(v_e_1869_);
lean_inc(v___y_1870_);
v___f_1896_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1896_, 0, v___y_1870_);
lean_closure_set(v___f_1896_, 1, v_e_1869_);
lean_closure_set(v___f_1896_, 2, v_size_1895_);
v___x_1897_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1898_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1897_, v___f_1896_, v___y_1871_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v___x_1899_; 
lean_dec_ref(v___x_1898_);
lean_inc_ref(v_e_1869_);
v___x_1899_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1869_, v___y_1870_, v___y_1871_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v___x_1900_; 
lean_dec_ref(v___x_1899_);
v___x_1900_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1897_, v_e_1869_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1907_ == 0)
{
lean_object* v_unused_1908_; 
v_unused_1908_ = lean_ctor_get(v___x_1900_, 0);
lean_dec(v_unused_1908_);
v___x_1902_ = v___x_1900_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_dec(v___x_1900_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v_size_1895_);
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_size_1895_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_size_1895_);
v_a_1909_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1900_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1900_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_size_1895_);
lean_dec_ref(v_e_1869_);
v_a_1917_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1899_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1899_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec(v_size_1895_);
lean_dec_ref(v_e_1869_);
v_a_1925_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1898_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1898_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec_ref(v_e_1869_);
v_a_1934_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1882_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1882_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___boxed(lean_object* v_e_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec(v___y_1943_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar(lean_object* v_e_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar___boxed(lean_object* v_e_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVar(v_e_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec(v_a_1971_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_nat_to_int(v_a_1984_);
return v___x_1985_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object* v_msg_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; lean_object* v___f_2001_; lean_object* v___x_39892__overap_2002_; lean_object* v___x_2003_; 
v___x_2000_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0);
v___f_2001_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2001_, 0, v___x_2000_);
v___x_39892__overap_2002_ = lean_panic_fn_borrowed(v___f_2001_, v_msg_1987_);
lean_dec_ref(v___f_2001_);
lean_inc(v___y_1998_);
lean_inc_ref(v___y_1997_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1995_);
lean_inc(v___y_1994_);
lean_inc_ref(v___y_1993_);
lean_inc(v___y_1992_);
lean_inc_ref(v___y_1991_);
lean_inc(v___y_1990_);
lean_inc(v___y_1989_);
lean_inc(v___y_1988_);
v___x_2003_ = lean_apply_12(v___x_39892__overap_2002_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, lean_box(0));
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object* v_msg_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v_msg_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec(v___y_2005_);
return v_res_2017_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0));
v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(lean_object* v_type_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2027_; 
lean_inc_ref(v_type_2021_);
v___x_2027_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2040_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2040_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2040_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
if (lean_obj_tag(v_a_2028_) == 1)
{
lean_object* v_val_2032_; lean_object* v___x_2034_; 
lean_dec_ref(v_type_2021_);
v_val_2032_ = lean_ctor_get(v_a_2028_, 0);
lean_inc(v_val_2032_);
lean_dec_ref(v_a_2028_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v_val_2032_);
v___x_2034_ = v___x_2030_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_val_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_del_object(v___x_2030_);
lean_dec(v_a_2028_);
v___x_2036_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1);
v___x_2037_ = l_Lean_indentExpr(v_type_2021_);
v___x_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_2038_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
return v___x_2039_;
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v_type_2021_);
v_a_2041_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2027_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2027_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_type_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(lean_object* v_type_2056_, lean_object* v_u_2057_, lean_object* v_instDeclName_2058_, lean_object* v_declName_2059_, lean_object* v_expectedInst_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2073_ = lean_box(0);
lean_inc_n(v_u_2057_, 2);
v___x_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_u_2057_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_u_2057_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2076_, 0, v_u_2057_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
lean_inc_ref(v___x_2076_);
v___x_2077_ = l_Lean_mkConst(v_instDeclName_2058_, v___x_2076_);
lean_inc_ref_n(v_type_2056_, 3);
v___x_2078_ = l_Lean_mkApp3(v___x_2077_, v_type_2056_, v_type_2056_, v_type_2056_);
v___x_2079_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2078_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2081_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc_n(v_a_2080_, 2);
lean_dec_ref(v___x_2079_);
lean_inc(v_declName_2059_);
v___x_2081_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2059_, v_a_2080_, v_expectedInst_2060_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_dec_ref(v___x_2081_);
v___x_2082_ = l_Lean_mkConst(v_declName_2059_, v___x_2076_);
lean_inc_ref_n(v_type_2056_, 2);
v___x_2083_ = l_Lean_mkApp4(v___x_2082_, v_type_2056_, v_type_2056_, v_type_2056_, v_a_2080_);
v___x_2084_ = l_Lean_Meta_Sym_canon(v___x_2083_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2086_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2084_);
v___x_2086_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2085_, v___y_2067_);
return v___x_2086_;
}
else
{
return v___x_2084_;
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_a_2080_);
lean_dec_ref(v___x_2076_);
lean_dec(v_declName_2059_);
lean_dec_ref(v_type_2056_);
v_a_2087_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2081_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2081_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_expectedInst_2060_);
lean_dec(v_declName_2059_);
lean_dec_ref(v_type_2056_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_type_2095_ = _args[0];
lean_object* v_u_2096_ = _args[1];
lean_object* v_instDeclName_2097_ = _args[2];
lean_object* v_declName_2098_ = _args[3];
lean_object* v_expectedInst_2099_ = _args[4];
lean_object* v___y_2100_ = _args[5];
lean_object* v___y_2101_ = _args[6];
lean_object* v___y_2102_ = _args[7];
lean_object* v___y_2103_ = _args[8];
lean_object* v___y_2104_ = _args[9];
lean_object* v___y_2105_ = _args[10];
lean_object* v___y_2106_ = _args[11];
lean_object* v___y_2107_ = _args[12];
lean_object* v___y_2108_ = _args[13];
lean_object* v___y_2109_ = _args[14];
lean_object* v___y_2110_ = _args[15];
lean_object* v___y_2111_ = _args[16];
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2095_, v_u_2096_, v_instDeclName_2097_, v_declName_2098_, v_expectedInst_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec(v___y_2100_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object* v_a_2113_, lean_object* v_s_2114_){
_start:
{
lean_object* v_toRing_2115_; lean_object* v_invFn_x3f_2116_; lean_object* v_semiringId_x3f_2117_; lean_object* v_commSemiringInst_2118_; lean_object* v_commRingInst_2119_; lean_object* v_noZeroDivInst_x3f_2120_; lean_object* v_fieldInst_x3f_2121_; lean_object* v_denoteEntries_2122_; lean_object* v_nextId_2123_; lean_object* v_steps_2124_; lean_object* v_queue_2125_; lean_object* v_basis_2126_; lean_object* v_diseqs_2127_; uint8_t v_recheck_2128_; lean_object* v_invSet_2129_; lean_object* v_numEq0_x3f_2130_; uint8_t v_numEq0Updated_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2163_; 
v_toRing_2115_ = lean_ctor_get(v_s_2114_, 0);
v_invFn_x3f_2116_ = lean_ctor_get(v_s_2114_, 1);
v_semiringId_x3f_2117_ = lean_ctor_get(v_s_2114_, 2);
v_commSemiringInst_2118_ = lean_ctor_get(v_s_2114_, 3);
v_commRingInst_2119_ = lean_ctor_get(v_s_2114_, 4);
v_noZeroDivInst_x3f_2120_ = lean_ctor_get(v_s_2114_, 5);
v_fieldInst_x3f_2121_ = lean_ctor_get(v_s_2114_, 6);
v_denoteEntries_2122_ = lean_ctor_get(v_s_2114_, 7);
v_nextId_2123_ = lean_ctor_get(v_s_2114_, 8);
v_steps_2124_ = lean_ctor_get(v_s_2114_, 9);
v_queue_2125_ = lean_ctor_get(v_s_2114_, 10);
v_basis_2126_ = lean_ctor_get(v_s_2114_, 11);
v_diseqs_2127_ = lean_ctor_get(v_s_2114_, 12);
v_recheck_2128_ = lean_ctor_get_uint8(v_s_2114_, sizeof(void*)*15);
v_invSet_2129_ = lean_ctor_get(v_s_2114_, 13);
v_numEq0_x3f_2130_ = lean_ctor_get(v_s_2114_, 14);
v_numEq0Updated_2131_ = lean_ctor_get_uint8(v_s_2114_, sizeof(void*)*15 + 1);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_s_2114_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2133_ = v_s_2114_;
v_isShared_2134_ = v_isSharedCheck_2163_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_numEq0_x3f_2130_);
lean_inc(v_invSet_2129_);
lean_inc(v_diseqs_2127_);
lean_inc(v_basis_2126_);
lean_inc(v_queue_2125_);
lean_inc(v_steps_2124_);
lean_inc(v_nextId_2123_);
lean_inc(v_denoteEntries_2122_);
lean_inc(v_fieldInst_x3f_2121_);
lean_inc(v_noZeroDivInst_x3f_2120_);
lean_inc(v_commRingInst_2119_);
lean_inc(v_commSemiringInst_2118_);
lean_inc(v_semiringId_x3f_2117_);
lean_inc(v_invFn_x3f_2116_);
lean_inc(v_toRing_2115_);
lean_dec(v_s_2114_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2163_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_id_2135_; lean_object* v_type_2136_; lean_object* v_u_2137_; lean_object* v_ringInst_2138_; lean_object* v_semiringInst_2139_; lean_object* v_charInst_x3f_2140_; lean_object* v_addFn_x3f_2141_; lean_object* v_subFn_x3f_2142_; lean_object* v_negFn_x3f_2143_; lean_object* v_powFn_x3f_2144_; lean_object* v_intCastFn_x3f_2145_; lean_object* v_natCastFn_x3f_2146_; lean_object* v_one_x3f_2147_; lean_object* v_vars_2148_; lean_object* v_varMap_2149_; lean_object* v_denote_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2161_; 
v_id_2135_ = lean_ctor_get(v_toRing_2115_, 0);
v_type_2136_ = lean_ctor_get(v_toRing_2115_, 1);
v_u_2137_ = lean_ctor_get(v_toRing_2115_, 2);
v_ringInst_2138_ = lean_ctor_get(v_toRing_2115_, 3);
v_semiringInst_2139_ = lean_ctor_get(v_toRing_2115_, 4);
v_charInst_x3f_2140_ = lean_ctor_get(v_toRing_2115_, 5);
v_addFn_x3f_2141_ = lean_ctor_get(v_toRing_2115_, 6);
v_subFn_x3f_2142_ = lean_ctor_get(v_toRing_2115_, 8);
v_negFn_x3f_2143_ = lean_ctor_get(v_toRing_2115_, 9);
v_powFn_x3f_2144_ = lean_ctor_get(v_toRing_2115_, 10);
v_intCastFn_x3f_2145_ = lean_ctor_get(v_toRing_2115_, 11);
v_natCastFn_x3f_2146_ = lean_ctor_get(v_toRing_2115_, 12);
v_one_x3f_2147_ = lean_ctor_get(v_toRing_2115_, 13);
v_vars_2148_ = lean_ctor_get(v_toRing_2115_, 14);
v_varMap_2149_ = lean_ctor_get(v_toRing_2115_, 15);
v_denote_2150_ = lean_ctor_get(v_toRing_2115_, 16);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_toRing_2115_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v_toRing_2115_, 7);
lean_dec(v_unused_2162_);
v___x_2152_ = v_toRing_2115_;
v_isShared_2153_ = v_isSharedCheck_2161_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_denote_2150_);
lean_inc(v_varMap_2149_);
lean_inc(v_vars_2148_);
lean_inc(v_one_x3f_2147_);
lean_inc(v_natCastFn_x3f_2146_);
lean_inc(v_intCastFn_x3f_2145_);
lean_inc(v_powFn_x3f_2144_);
lean_inc(v_negFn_x3f_2143_);
lean_inc(v_subFn_x3f_2142_);
lean_inc(v_addFn_x3f_2141_);
lean_inc(v_charInst_x3f_2140_);
lean_inc(v_semiringInst_2139_);
lean_inc(v_ringInst_2138_);
lean_inc(v_u_2137_);
lean_inc(v_type_2136_);
lean_inc(v_id_2135_);
lean_dec(v_toRing_2115_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2161_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2154_, 0, v_a_2113_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 7, v___x_2154_);
v___x_2156_ = v___x_2152_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_id_2135_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_type_2136_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_u_2137_);
lean_ctor_set(v_reuseFailAlloc_2160_, 3, v_ringInst_2138_);
lean_ctor_set(v_reuseFailAlloc_2160_, 4, v_semiringInst_2139_);
lean_ctor_set(v_reuseFailAlloc_2160_, 5, v_charInst_x3f_2140_);
lean_ctor_set(v_reuseFailAlloc_2160_, 6, v_addFn_x3f_2141_);
lean_ctor_set(v_reuseFailAlloc_2160_, 7, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2160_, 8, v_subFn_x3f_2142_);
lean_ctor_set(v_reuseFailAlloc_2160_, 9, v_negFn_x3f_2143_);
lean_ctor_set(v_reuseFailAlloc_2160_, 10, v_powFn_x3f_2144_);
lean_ctor_set(v_reuseFailAlloc_2160_, 11, v_intCastFn_x3f_2145_);
lean_ctor_set(v_reuseFailAlloc_2160_, 12, v_natCastFn_x3f_2146_);
lean_ctor_set(v_reuseFailAlloc_2160_, 13, v_one_x3f_2147_);
lean_ctor_set(v_reuseFailAlloc_2160_, 14, v_vars_2148_);
lean_ctor_set(v_reuseFailAlloc_2160_, 15, v_varMap_2149_);
lean_ctor_set(v_reuseFailAlloc_2160_, 16, v_denote_2150_);
v___x_2156_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2158_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2156_);
v___x_2158_ = v___x_2133_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_invFn_x3f_2116_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_semiringId_x3f_2117_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_commSemiringInst_2118_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v_commRingInst_2119_);
lean_ctor_set(v_reuseFailAlloc_2159_, 5, v_noZeroDivInst_x3f_2120_);
lean_ctor_set(v_reuseFailAlloc_2159_, 6, v_fieldInst_x3f_2121_);
lean_ctor_set(v_reuseFailAlloc_2159_, 7, v_denoteEntries_2122_);
lean_ctor_set(v_reuseFailAlloc_2159_, 8, v_nextId_2123_);
lean_ctor_set(v_reuseFailAlloc_2159_, 9, v_steps_2124_);
lean_ctor_set(v_reuseFailAlloc_2159_, 10, v_queue_2125_);
lean_ctor_set(v_reuseFailAlloc_2159_, 11, v_basis_2126_);
lean_ctor_set(v_reuseFailAlloc_2159_, 12, v_diseqs_2127_);
lean_ctor_set(v_reuseFailAlloc_2159_, 13, v_invSet_2129_);
lean_ctor_set(v_reuseFailAlloc_2159_, 14, v_numEq0_x3f_2130_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, sizeof(void*)*15, v_recheck_2128_);
lean_ctor_set_uint8(v_reuseFailAlloc_2159_, sizeof(void*)*15 + 1, v_numEq0Updated_2131_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2220_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2220_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2220_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_toRing_2181_; lean_object* v_mulFn_x3f_2182_; 
v_toRing_2181_ = lean_ctor_get(v_a_2177_, 0);
lean_inc_ref(v_toRing_2181_);
lean_dec(v_a_2177_);
v_mulFn_x3f_2182_ = lean_ctor_get(v_toRing_2181_, 7);
if (lean_obj_tag(v_mulFn_x3f_2182_) == 1)
{
lean_object* v_val_2183_; lean_object* v___x_2185_; 
lean_inc_ref(v_mulFn_x3f_2182_);
lean_dec_ref(v_toRing_2181_);
v_val_2183_ = lean_ctor_get(v_mulFn_x3f_2182_, 0);
lean_inc(v_val_2183_);
lean_dec_ref(v_mulFn_x3f_2182_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v_val_2183_);
v___x_2185_ = v___x_2179_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_val_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
else
{
lean_object* v_type_2187_; lean_object* v_u_2188_; lean_object* v_semiringInst_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v_expectedInst_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_del_object(v___x_2179_);
v_type_2187_ = lean_ctor_get(v_toRing_2181_, 1);
lean_inc_ref_n(v_type_2187_, 3);
v_u_2188_ = lean_ctor_get(v_toRing_2181_, 2);
lean_inc_n(v_u_2188_, 2);
v_semiringInst_2189_ = lean_ctor_get(v_toRing_2181_, 4);
lean_inc_ref(v_semiringInst_2189_);
lean_dec_ref(v_toRing_2181_);
v___x_2190_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2192_, 0, v_u_2188_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
lean_inc_ref(v___x_2192_);
v___x_2193_ = l_Lean_mkConst(v___x_2190_, v___x_2192_);
v___x_2194_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_2195_ = l_Lean_mkConst(v___x_2194_, v___x_2192_);
v___x_2196_ = l_Lean_mkAppB(v___x_2195_, v_type_2187_, v_semiringInst_2189_);
v_expectedInst_2197_ = l_Lean_mkAppB(v___x_2193_, v_type_2187_, v___x_2196_);
v___x_2198_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5));
v___x_2199_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7));
v___x_2200_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2187_, v_u_2188_, v___x_2198_, v___x_2199_, v_expectedInst_2197_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___f_2202_; lean_object* v___x_2203_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc_n(v_a_2201_, 2);
lean_dec_ref(v___x_2200_);
v___f_2202_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2202_, 0, v_a_2201_);
v___x_2203_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2202_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; 
v_unused_2211_ = lean_ctor_get(v___x_2203_, 0);
lean_dec(v_unused_2211_);
v___x_2205_ = v___x_2203_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_dec(v___x_2203_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v_a_2201_);
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2201_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_a_2201_);
v_a_2212_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2203_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2203_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
return v___x_2200_;
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
v_a_2221_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2176_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2176_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec(v___y_2229_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object* v_a_2242_, lean_object* v_s_2243_){
_start:
{
lean_object* v_toRing_2244_; lean_object* v_invFn_x3f_2245_; lean_object* v_semiringId_x3f_2246_; lean_object* v_commSemiringInst_2247_; lean_object* v_commRingInst_2248_; lean_object* v_noZeroDivInst_x3f_2249_; lean_object* v_fieldInst_x3f_2250_; lean_object* v_denoteEntries_2251_; lean_object* v_nextId_2252_; lean_object* v_steps_2253_; lean_object* v_queue_2254_; lean_object* v_basis_2255_; lean_object* v_diseqs_2256_; uint8_t v_recheck_2257_; lean_object* v_invSet_2258_; lean_object* v_numEq0_x3f_2259_; uint8_t v_numEq0Updated_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2292_; 
v_toRing_2244_ = lean_ctor_get(v_s_2243_, 0);
v_invFn_x3f_2245_ = lean_ctor_get(v_s_2243_, 1);
v_semiringId_x3f_2246_ = lean_ctor_get(v_s_2243_, 2);
v_commSemiringInst_2247_ = lean_ctor_get(v_s_2243_, 3);
v_commRingInst_2248_ = lean_ctor_get(v_s_2243_, 4);
v_noZeroDivInst_x3f_2249_ = lean_ctor_get(v_s_2243_, 5);
v_fieldInst_x3f_2250_ = lean_ctor_get(v_s_2243_, 6);
v_denoteEntries_2251_ = lean_ctor_get(v_s_2243_, 7);
v_nextId_2252_ = lean_ctor_get(v_s_2243_, 8);
v_steps_2253_ = lean_ctor_get(v_s_2243_, 9);
v_queue_2254_ = lean_ctor_get(v_s_2243_, 10);
v_basis_2255_ = lean_ctor_get(v_s_2243_, 11);
v_diseqs_2256_ = lean_ctor_get(v_s_2243_, 12);
v_recheck_2257_ = lean_ctor_get_uint8(v_s_2243_, sizeof(void*)*15);
v_invSet_2258_ = lean_ctor_get(v_s_2243_, 13);
v_numEq0_x3f_2259_ = lean_ctor_get(v_s_2243_, 14);
v_numEq0Updated_2260_ = lean_ctor_get_uint8(v_s_2243_, sizeof(void*)*15 + 1);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_s_2243_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2262_ = v_s_2243_;
v_isShared_2263_ = v_isSharedCheck_2292_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_numEq0_x3f_2259_);
lean_inc(v_invSet_2258_);
lean_inc(v_diseqs_2256_);
lean_inc(v_basis_2255_);
lean_inc(v_queue_2254_);
lean_inc(v_steps_2253_);
lean_inc(v_nextId_2252_);
lean_inc(v_denoteEntries_2251_);
lean_inc(v_fieldInst_x3f_2250_);
lean_inc(v_noZeroDivInst_x3f_2249_);
lean_inc(v_commRingInst_2248_);
lean_inc(v_commSemiringInst_2247_);
lean_inc(v_semiringId_x3f_2246_);
lean_inc(v_invFn_x3f_2245_);
lean_inc(v_toRing_2244_);
lean_dec(v_s_2243_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2292_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v_id_2264_; lean_object* v_type_2265_; lean_object* v_u_2266_; lean_object* v_ringInst_2267_; lean_object* v_semiringInst_2268_; lean_object* v_charInst_x3f_2269_; lean_object* v_mulFn_x3f_2270_; lean_object* v_subFn_x3f_2271_; lean_object* v_negFn_x3f_2272_; lean_object* v_powFn_x3f_2273_; lean_object* v_intCastFn_x3f_2274_; lean_object* v_natCastFn_x3f_2275_; lean_object* v_one_x3f_2276_; lean_object* v_vars_2277_; lean_object* v_varMap_2278_; lean_object* v_denote_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2290_; 
v_id_2264_ = lean_ctor_get(v_toRing_2244_, 0);
v_type_2265_ = lean_ctor_get(v_toRing_2244_, 1);
v_u_2266_ = lean_ctor_get(v_toRing_2244_, 2);
v_ringInst_2267_ = lean_ctor_get(v_toRing_2244_, 3);
v_semiringInst_2268_ = lean_ctor_get(v_toRing_2244_, 4);
v_charInst_x3f_2269_ = lean_ctor_get(v_toRing_2244_, 5);
v_mulFn_x3f_2270_ = lean_ctor_get(v_toRing_2244_, 7);
v_subFn_x3f_2271_ = lean_ctor_get(v_toRing_2244_, 8);
v_negFn_x3f_2272_ = lean_ctor_get(v_toRing_2244_, 9);
v_powFn_x3f_2273_ = lean_ctor_get(v_toRing_2244_, 10);
v_intCastFn_x3f_2274_ = lean_ctor_get(v_toRing_2244_, 11);
v_natCastFn_x3f_2275_ = lean_ctor_get(v_toRing_2244_, 12);
v_one_x3f_2276_ = lean_ctor_get(v_toRing_2244_, 13);
v_vars_2277_ = lean_ctor_get(v_toRing_2244_, 14);
v_varMap_2278_ = lean_ctor_get(v_toRing_2244_, 15);
v_denote_2279_ = lean_ctor_get(v_toRing_2244_, 16);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_toRing_2244_);
if (v_isSharedCheck_2290_ == 0)
{
lean_object* v_unused_2291_; 
v_unused_2291_ = lean_ctor_get(v_toRing_2244_, 6);
lean_dec(v_unused_2291_);
v___x_2281_ = v_toRing_2244_;
v_isShared_2282_ = v_isSharedCheck_2290_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_denote_2279_);
lean_inc(v_varMap_2278_);
lean_inc(v_vars_2277_);
lean_inc(v_one_x3f_2276_);
lean_inc(v_natCastFn_x3f_2275_);
lean_inc(v_intCastFn_x3f_2274_);
lean_inc(v_powFn_x3f_2273_);
lean_inc(v_negFn_x3f_2272_);
lean_inc(v_subFn_x3f_2271_);
lean_inc(v_mulFn_x3f_2270_);
lean_inc(v_charInst_x3f_2269_);
lean_inc(v_semiringInst_2268_);
lean_inc(v_ringInst_2267_);
lean_inc(v_u_2266_);
lean_inc(v_type_2265_);
lean_inc(v_id_2264_);
lean_dec(v_toRing_2244_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2290_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2283_, 0, v_a_2242_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 6, v___x_2283_);
v___x_2285_ = v___x_2281_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_id_2264_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_type_2265_);
lean_ctor_set(v_reuseFailAlloc_2289_, 2, v_u_2266_);
lean_ctor_set(v_reuseFailAlloc_2289_, 3, v_ringInst_2267_);
lean_ctor_set(v_reuseFailAlloc_2289_, 4, v_semiringInst_2268_);
lean_ctor_set(v_reuseFailAlloc_2289_, 5, v_charInst_x3f_2269_);
lean_ctor_set(v_reuseFailAlloc_2289_, 6, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2289_, 7, v_mulFn_x3f_2270_);
lean_ctor_set(v_reuseFailAlloc_2289_, 8, v_subFn_x3f_2271_);
lean_ctor_set(v_reuseFailAlloc_2289_, 9, v_negFn_x3f_2272_);
lean_ctor_set(v_reuseFailAlloc_2289_, 10, v_powFn_x3f_2273_);
lean_ctor_set(v_reuseFailAlloc_2289_, 11, v_intCastFn_x3f_2274_);
lean_ctor_set(v_reuseFailAlloc_2289_, 12, v_natCastFn_x3f_2275_);
lean_ctor_set(v_reuseFailAlloc_2289_, 13, v_one_x3f_2276_);
lean_ctor_set(v_reuseFailAlloc_2289_, 14, v_vars_2277_);
lean_ctor_set(v_reuseFailAlloc_2289_, 15, v_varMap_2278_);
lean_ctor_set(v_reuseFailAlloc_2289_, 16, v_denote_2279_);
v___x_2285_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2287_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2285_);
v___x_2287_ = v___x_2262_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_invFn_x3f_2245_);
lean_ctor_set(v_reuseFailAlloc_2288_, 2, v_semiringId_x3f_2246_);
lean_ctor_set(v_reuseFailAlloc_2288_, 3, v_commSemiringInst_2247_);
lean_ctor_set(v_reuseFailAlloc_2288_, 4, v_commRingInst_2248_);
lean_ctor_set(v_reuseFailAlloc_2288_, 5, v_noZeroDivInst_x3f_2249_);
lean_ctor_set(v_reuseFailAlloc_2288_, 6, v_fieldInst_x3f_2250_);
lean_ctor_set(v_reuseFailAlloc_2288_, 7, v_denoteEntries_2251_);
lean_ctor_set(v_reuseFailAlloc_2288_, 8, v_nextId_2252_);
lean_ctor_set(v_reuseFailAlloc_2288_, 9, v_steps_2253_);
lean_ctor_set(v_reuseFailAlloc_2288_, 10, v_queue_2254_);
lean_ctor_set(v_reuseFailAlloc_2288_, 11, v_basis_2255_);
lean_ctor_set(v_reuseFailAlloc_2288_, 12, v_diseqs_2256_);
lean_ctor_set(v_reuseFailAlloc_2288_, 13, v_invSet_2258_);
lean_ctor_set(v_reuseFailAlloc_2288_, 14, v_numEq0_x3f_2259_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*15, v_recheck_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2288_, sizeof(void*)*15 + 1, v_numEq0Updated_2260_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2349_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2349_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2349_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v_toRing_2310_; lean_object* v_addFn_x3f_2311_; 
v_toRing_2310_ = lean_ctor_get(v_a_2306_, 0);
lean_inc_ref(v_toRing_2310_);
lean_dec(v_a_2306_);
v_addFn_x3f_2311_ = lean_ctor_get(v_toRing_2310_, 6);
if (lean_obj_tag(v_addFn_x3f_2311_) == 1)
{
lean_object* v_val_2312_; lean_object* v___x_2314_; 
lean_inc_ref(v_addFn_x3f_2311_);
lean_dec_ref(v_toRing_2310_);
v_val_2312_ = lean_ctor_get(v_addFn_x3f_2311_, 0);
lean_inc(v_val_2312_);
lean_dec_ref(v_addFn_x3f_2311_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v_val_2312_);
v___x_2314_ = v___x_2308_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_val_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
else
{
lean_object* v_type_2316_; lean_object* v_u_2317_; lean_object* v_semiringInst_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v_expectedInst_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_del_object(v___x_2308_);
v_type_2316_ = lean_ctor_get(v_toRing_2310_, 1);
lean_inc_ref_n(v_type_2316_, 3);
v_u_2317_ = lean_ctor_get(v_toRing_2310_, 2);
lean_inc_n(v_u_2317_, 2);
v_semiringInst_2318_ = lean_ctor_get(v_toRing_2310_, 4);
lean_inc_ref(v_semiringInst_2318_);
lean_dec_ref(v_toRing_2310_);
v___x_2319_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2321_, 0, v_u_2317_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
lean_inc_ref(v___x_2321_);
v___x_2322_ = l_Lean_mkConst(v___x_2319_, v___x_2321_);
v___x_2323_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_2324_ = l_Lean_mkConst(v___x_2323_, v___x_2321_);
v___x_2325_ = l_Lean_mkAppB(v___x_2324_, v_type_2316_, v_semiringInst_2318_);
v_expectedInst_2326_ = l_Lean_mkAppB(v___x_2322_, v_type_2316_, v___x_2325_);
v___x_2327_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6));
v___x_2328_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8));
v___x_2329_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2316_, v_u_2317_, v___x_2327_, v___x_2328_, v_expectedInst_2326_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___f_2331_; lean_object* v___x_2332_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc_n(v_a_2330_, 2);
lean_dec_ref(v___x_2329_);
v___f_2331_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_2331_, 0, v_a_2330_);
v___x_2332_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2331_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; 
v_unused_2340_ = lean_ctor_get(v___x_2332_, 0);
lean_dec(v_unused_2340_);
v___x_2334_ = v___x_2332_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_dec(v___x_2332_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v_a_2330_);
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2330_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_a_2330_);
v_a_2341_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2332_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2332_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
v_a_2350_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2305_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2305_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec(v___y_2358_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(lean_object* v_type_2371_, lean_object* v_u_2372_, lean_object* v_instDeclName_2373_, lean_object* v_declName_2374_, lean_object* v_expectedInst_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2388_ = lean_box(0);
v___x_2389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2389_, 0, v_u_2372_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
lean_inc_ref(v___x_2389_);
v___x_2390_ = l_Lean_mkConst(v_instDeclName_2373_, v___x_2389_);
lean_inc_ref(v_type_2371_);
v___x_2391_ = l_Lean_Expr_app___override(v___x_2390_, v_type_2371_);
v___x_2392_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2391_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2394_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc_n(v_a_2393_, 2);
lean_dec_ref(v___x_2392_);
lean_inc(v_declName_2374_);
v___x_2394_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2374_, v_a_2393_, v_expectedInst_2375_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
lean_dec_ref(v___x_2394_);
v___x_2395_ = l_Lean_mkConst(v_declName_2374_, v___x_2389_);
v___x_2396_ = l_Lean_mkAppB(v___x_2395_, v_type_2371_, v_a_2393_);
v___x_2397_ = l_Lean_Meta_Sym_canon(v___x_2396_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2399_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref(v___x_2397_);
v___x_2399_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2398_, v___y_2382_);
return v___x_2399_;
}
else
{
return v___x_2397_;
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec(v_a_2393_);
lean_dec_ref(v___x_2389_);
lean_dec(v_declName_2374_);
lean_dec_ref(v_type_2371_);
v_a_2400_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2394_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2394_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
else
{
lean_dec_ref(v___x_2389_);
lean_dec_ref(v_expectedInst_2375_);
lean_dec(v_declName_2374_);
lean_dec_ref(v_type_2371_);
return v___x_2392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_type_2408_ = _args[0];
lean_object* v_u_2409_ = _args[1];
lean_object* v_instDeclName_2410_ = _args[2];
lean_object* v_declName_2411_ = _args[3];
lean_object* v_expectedInst_2412_ = _args[4];
lean_object* v___y_2413_ = _args[5];
lean_object* v___y_2414_ = _args[6];
lean_object* v___y_2415_ = _args[7];
lean_object* v___y_2416_ = _args[8];
lean_object* v___y_2417_ = _args[9];
lean_object* v___y_2418_ = _args[10];
lean_object* v___y_2419_ = _args[11];
lean_object* v___y_2420_ = _args[12];
lean_object* v___y_2421_ = _args[13];
lean_object* v___y_2422_ = _args[14];
lean_object* v___y_2423_ = _args[15];
lean_object* v___y_2424_ = _args[16];
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2408_, v_u_2409_, v_instDeclName_2410_, v_declName_2411_, v_expectedInst_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec(v___y_2413_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object* v_a_2426_, lean_object* v_s_2427_){
_start:
{
lean_object* v_toRing_2428_; lean_object* v_invFn_x3f_2429_; lean_object* v_semiringId_x3f_2430_; lean_object* v_commSemiringInst_2431_; lean_object* v_commRingInst_2432_; lean_object* v_noZeroDivInst_x3f_2433_; lean_object* v_fieldInst_x3f_2434_; lean_object* v_denoteEntries_2435_; lean_object* v_nextId_2436_; lean_object* v_steps_2437_; lean_object* v_queue_2438_; lean_object* v_basis_2439_; lean_object* v_diseqs_2440_; uint8_t v_recheck_2441_; lean_object* v_invSet_2442_; lean_object* v_numEq0_x3f_2443_; uint8_t v_numEq0Updated_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2476_; 
v_toRing_2428_ = lean_ctor_get(v_s_2427_, 0);
v_invFn_x3f_2429_ = lean_ctor_get(v_s_2427_, 1);
v_semiringId_x3f_2430_ = lean_ctor_get(v_s_2427_, 2);
v_commSemiringInst_2431_ = lean_ctor_get(v_s_2427_, 3);
v_commRingInst_2432_ = lean_ctor_get(v_s_2427_, 4);
v_noZeroDivInst_x3f_2433_ = lean_ctor_get(v_s_2427_, 5);
v_fieldInst_x3f_2434_ = lean_ctor_get(v_s_2427_, 6);
v_denoteEntries_2435_ = lean_ctor_get(v_s_2427_, 7);
v_nextId_2436_ = lean_ctor_get(v_s_2427_, 8);
v_steps_2437_ = lean_ctor_get(v_s_2427_, 9);
v_queue_2438_ = lean_ctor_get(v_s_2427_, 10);
v_basis_2439_ = lean_ctor_get(v_s_2427_, 11);
v_diseqs_2440_ = lean_ctor_get(v_s_2427_, 12);
v_recheck_2441_ = lean_ctor_get_uint8(v_s_2427_, sizeof(void*)*15);
v_invSet_2442_ = lean_ctor_get(v_s_2427_, 13);
v_numEq0_x3f_2443_ = lean_ctor_get(v_s_2427_, 14);
v_numEq0Updated_2444_ = lean_ctor_get_uint8(v_s_2427_, sizeof(void*)*15 + 1);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_s_2427_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2446_ = v_s_2427_;
v_isShared_2447_ = v_isSharedCheck_2476_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_numEq0_x3f_2443_);
lean_inc(v_invSet_2442_);
lean_inc(v_diseqs_2440_);
lean_inc(v_basis_2439_);
lean_inc(v_queue_2438_);
lean_inc(v_steps_2437_);
lean_inc(v_nextId_2436_);
lean_inc(v_denoteEntries_2435_);
lean_inc(v_fieldInst_x3f_2434_);
lean_inc(v_noZeroDivInst_x3f_2433_);
lean_inc(v_commRingInst_2432_);
lean_inc(v_commSemiringInst_2431_);
lean_inc(v_semiringId_x3f_2430_);
lean_inc(v_invFn_x3f_2429_);
lean_inc(v_toRing_2428_);
lean_dec(v_s_2427_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2476_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v_id_2448_; lean_object* v_type_2449_; lean_object* v_u_2450_; lean_object* v_ringInst_2451_; lean_object* v_semiringInst_2452_; lean_object* v_charInst_x3f_2453_; lean_object* v_addFn_x3f_2454_; lean_object* v_mulFn_x3f_2455_; lean_object* v_subFn_x3f_2456_; lean_object* v_powFn_x3f_2457_; lean_object* v_intCastFn_x3f_2458_; lean_object* v_natCastFn_x3f_2459_; lean_object* v_one_x3f_2460_; lean_object* v_vars_2461_; lean_object* v_varMap_2462_; lean_object* v_denote_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2474_; 
v_id_2448_ = lean_ctor_get(v_toRing_2428_, 0);
v_type_2449_ = lean_ctor_get(v_toRing_2428_, 1);
v_u_2450_ = lean_ctor_get(v_toRing_2428_, 2);
v_ringInst_2451_ = lean_ctor_get(v_toRing_2428_, 3);
v_semiringInst_2452_ = lean_ctor_get(v_toRing_2428_, 4);
v_charInst_x3f_2453_ = lean_ctor_get(v_toRing_2428_, 5);
v_addFn_x3f_2454_ = lean_ctor_get(v_toRing_2428_, 6);
v_mulFn_x3f_2455_ = lean_ctor_get(v_toRing_2428_, 7);
v_subFn_x3f_2456_ = lean_ctor_get(v_toRing_2428_, 8);
v_powFn_x3f_2457_ = lean_ctor_get(v_toRing_2428_, 10);
v_intCastFn_x3f_2458_ = lean_ctor_get(v_toRing_2428_, 11);
v_natCastFn_x3f_2459_ = lean_ctor_get(v_toRing_2428_, 12);
v_one_x3f_2460_ = lean_ctor_get(v_toRing_2428_, 13);
v_vars_2461_ = lean_ctor_get(v_toRing_2428_, 14);
v_varMap_2462_ = lean_ctor_get(v_toRing_2428_, 15);
v_denote_2463_ = lean_ctor_get(v_toRing_2428_, 16);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_toRing_2428_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v_toRing_2428_, 9);
lean_dec(v_unused_2475_);
v___x_2465_ = v_toRing_2428_;
v_isShared_2466_ = v_isSharedCheck_2474_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_denote_2463_);
lean_inc(v_varMap_2462_);
lean_inc(v_vars_2461_);
lean_inc(v_one_x3f_2460_);
lean_inc(v_natCastFn_x3f_2459_);
lean_inc(v_intCastFn_x3f_2458_);
lean_inc(v_powFn_x3f_2457_);
lean_inc(v_subFn_x3f_2456_);
lean_inc(v_mulFn_x3f_2455_);
lean_inc(v_addFn_x3f_2454_);
lean_inc(v_charInst_x3f_2453_);
lean_inc(v_semiringInst_2452_);
lean_inc(v_ringInst_2451_);
lean_inc(v_u_2450_);
lean_inc(v_type_2449_);
lean_inc(v_id_2448_);
lean_dec(v_toRing_2428_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2474_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2467_, 0, v_a_2426_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 9, v___x_2467_);
v___x_2469_ = v___x_2465_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_id_2448_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_type_2449_);
lean_ctor_set(v_reuseFailAlloc_2473_, 2, v_u_2450_);
lean_ctor_set(v_reuseFailAlloc_2473_, 3, v_ringInst_2451_);
lean_ctor_set(v_reuseFailAlloc_2473_, 4, v_semiringInst_2452_);
lean_ctor_set(v_reuseFailAlloc_2473_, 5, v_charInst_x3f_2453_);
lean_ctor_set(v_reuseFailAlloc_2473_, 6, v_addFn_x3f_2454_);
lean_ctor_set(v_reuseFailAlloc_2473_, 7, v_mulFn_x3f_2455_);
lean_ctor_set(v_reuseFailAlloc_2473_, 8, v_subFn_x3f_2456_);
lean_ctor_set(v_reuseFailAlloc_2473_, 9, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2473_, 10, v_powFn_x3f_2457_);
lean_ctor_set(v_reuseFailAlloc_2473_, 11, v_intCastFn_x3f_2458_);
lean_ctor_set(v_reuseFailAlloc_2473_, 12, v_natCastFn_x3f_2459_);
lean_ctor_set(v_reuseFailAlloc_2473_, 13, v_one_x3f_2460_);
lean_ctor_set(v_reuseFailAlloc_2473_, 14, v_vars_2461_);
lean_ctor_set(v_reuseFailAlloc_2473_, 15, v_varMap_2462_);
lean_ctor_set(v_reuseFailAlloc_2473_, 16, v_denote_2463_);
v___x_2469_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2471_; 
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2469_);
v___x_2471_ = v___x_2446_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_invFn_x3f_2429_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v_semiringId_x3f_2430_);
lean_ctor_set(v_reuseFailAlloc_2472_, 3, v_commSemiringInst_2431_);
lean_ctor_set(v_reuseFailAlloc_2472_, 4, v_commRingInst_2432_);
lean_ctor_set(v_reuseFailAlloc_2472_, 5, v_noZeroDivInst_x3f_2433_);
lean_ctor_set(v_reuseFailAlloc_2472_, 6, v_fieldInst_x3f_2434_);
lean_ctor_set(v_reuseFailAlloc_2472_, 7, v_denoteEntries_2435_);
lean_ctor_set(v_reuseFailAlloc_2472_, 8, v_nextId_2436_);
lean_ctor_set(v_reuseFailAlloc_2472_, 9, v_steps_2437_);
lean_ctor_set(v_reuseFailAlloc_2472_, 10, v_queue_2438_);
lean_ctor_set(v_reuseFailAlloc_2472_, 11, v_basis_2439_);
lean_ctor_set(v_reuseFailAlloc_2472_, 12, v_diseqs_2440_);
lean_ctor_set(v_reuseFailAlloc_2472_, 13, v_invSet_2442_);
lean_ctor_set(v_reuseFailAlloc_2472_, 14, v_numEq0_x3f_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2472_, sizeof(void*)*15, v_recheck_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2472_, sizeof(void*)*15 + 1, v_numEq0Updated_2444_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2543_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2505_ = v___x_2502_;
v_isShared_2506_ = v_isSharedCheck_2543_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2502_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2543_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v_toRing_2507_; lean_object* v_negFn_x3f_2508_; 
v_toRing_2507_ = lean_ctor_get(v_a_2503_, 0);
lean_inc_ref(v_toRing_2507_);
lean_dec(v_a_2503_);
v_negFn_x3f_2508_ = lean_ctor_get(v_toRing_2507_, 9);
if (lean_obj_tag(v_negFn_x3f_2508_) == 1)
{
lean_object* v_val_2509_; lean_object* v___x_2511_; 
lean_inc_ref(v_negFn_x3f_2508_);
lean_dec_ref(v_toRing_2507_);
v_val_2509_ = lean_ctor_get(v_negFn_x3f_2508_, 0);
lean_inc(v_val_2509_);
lean_dec_ref(v_negFn_x3f_2508_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 0, v_val_2509_);
v___x_2511_ = v___x_2505_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_val_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
else
{
lean_object* v_type_2513_; lean_object* v_u_2514_; lean_object* v_ringInst_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v_expectedInst_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_del_object(v___x_2505_);
v_type_2513_ = lean_ctor_get(v_toRing_2507_, 1);
lean_inc_ref_n(v_type_2513_, 2);
v_u_2514_ = lean_ctor_get(v_toRing_2507_, 2);
lean_inc_n(v_u_2514_, 2);
v_ringInst_2515_ = lean_ctor_get(v_toRing_2507_, 3);
lean_inc_ref(v_ringInst_2515_);
lean_dec_ref(v_toRing_2507_);
v___x_2516_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1));
v___x_2517_ = lean_box(0);
v___x_2518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2518_, 0, v_u_2514_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = l_Lean_mkConst(v___x_2516_, v___x_2518_);
v_expectedInst_2520_ = l_Lean_mkAppB(v___x_2519_, v_type_2513_, v_ringInst_2515_);
v___x_2521_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3));
v___x_2522_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5));
v___x_2523_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2513_, v_u_2514_, v___x_2521_, v___x_2522_, v_expectedInst_2520_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___f_2525_; lean_object* v___x_2526_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc_n(v_a_2524_, 2);
lean_dec_ref(v___x_2523_);
v___f_2525_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_2525_, 0, v_a_2524_);
v___x_2526_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2525_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v___x_2526_, 0);
lean_dec(v_unused_2534_);
v___x_2528_ = v___x_2526_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_dec(v___x_2526_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v_a_2524_);
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2524_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_a_2524_);
v_a_2535_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2526_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2526_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
v_a_2544_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2502_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2502_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec(v___y_2552_);
return v_res_2564_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = lean_unsigned_to_nat(0u);
v___x_2573_ = lean_nat_to_int(v___x_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(lean_object* v_k_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v_toRing_2594_; lean_object* v_type_2595_; lean_object* v_u_2596_; lean_object* v_semiringInst_2597_; lean_object* v___x_2598_; lean_object* v_n_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref(v___x_2592_);
v_toRing_2594_ = lean_ctor_get(v_a_2593_, 0);
lean_inc_ref(v_toRing_2594_);
lean_dec(v_a_2593_);
v_type_2595_ = lean_ctor_get(v_toRing_2594_, 1);
lean_inc_ref_n(v_type_2595_, 2);
v_u_2596_ = lean_ctor_get(v_toRing_2594_, 2);
lean_inc(v_u_2596_);
v_semiringInst_2597_ = lean_ctor_get(v_toRing_2594_, 4);
lean_inc_ref(v_semiringInst_2597_);
lean_dec_ref(v_toRing_2594_);
v___x_2598_ = lean_nat_abs(v_k_2579_);
v_n_2599_ = l_Lean_mkRawNatLit(v___x_2598_);
v___x_2600_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1));
v___x_2601_ = lean_box(0);
v___x_2602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2602_, 0, v_u_2596_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
lean_inc_ref(v___x_2602_);
v___x_2603_ = l_Lean_mkConst(v___x_2600_, v___x_2602_);
lean_inc_ref(v_n_2599_);
v___x_2604_ = l_Lean_mkAppB(v___x_2603_, v_type_2595_, v_n_2599_);
v___x_2605_ = lean_box(0);
v___x_2606_ = l_Lean_Meta_synthInstance_x3f(v___x_2604_, v___x_2605_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2646_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2646_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2646_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v_ofNatInst_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; 
if (lean_obj_tag(v_a_2607_) == 1)
{
lean_object* v_val_2642_; 
lean_dec_ref(v_semiringInst_2597_);
v_val_2642_ = lean_ctor_get(v_a_2607_, 0);
lean_inc(v_val_2642_);
lean_dec_ref(v_a_2607_);
v_ofNatInst_2612_ = v_val_2642_;
v___y_2613_ = v___y_2580_;
v___y_2614_ = v___y_2581_;
v___y_2615_ = v___y_2582_;
v___y_2616_ = v___y_2583_;
v___y_2617_ = v___y_2584_;
v___y_2618_ = v___y_2585_;
v___y_2619_ = v___y_2586_;
v___y_2620_ = v___y_2587_;
v___y_2621_ = v___y_2588_;
v___y_2622_ = v___y_2589_;
v___y_2623_ = v___y_2590_;
goto v___jp_2611_;
}
else
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_dec(v_a_2607_);
v___x_2643_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5));
lean_inc_ref(v___x_2602_);
v___x_2644_ = l_Lean_mkConst(v___x_2643_, v___x_2602_);
lean_inc_ref(v_n_2599_);
lean_inc_ref(v_type_2595_);
v___x_2645_ = l_Lean_mkApp3(v___x_2644_, v_type_2595_, v_semiringInst_2597_, v_n_2599_);
v_ofNatInst_2612_ = v___x_2645_;
v___y_2613_ = v___y_2580_;
v___y_2614_ = v___y_2581_;
v___y_2615_ = v___y_2582_;
v___y_2616_ = v___y_2583_;
v___y_2617_ = v___y_2584_;
v___y_2618_ = v___y_2585_;
v___y_2619_ = v___y_2586_;
v___y_2620_ = v___y_2587_;
v___y_2621_ = v___y_2588_;
v___y_2622_ = v___y_2589_;
v___y_2623_ = v___y_2590_;
goto v___jp_2611_;
}
v___jp_2611_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v_n_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2624_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3));
v___x_2625_ = l_Lean_mkConst(v___x_2624_, v___x_2602_);
v_n_2626_ = l_Lean_mkApp3(v___x_2625_, v_type_2595_, v_n_2599_, v_ofNatInst_2612_);
v___x_2627_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4);
v___x_2628_ = lean_int_dec_lt(v_k_2579_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2630_; 
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v_n_2626_);
v___x_2630_ = v___x_2609_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_n_2626_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
else
{
lean_object* v___x_2632_; 
lean_del_object(v___x_2609_);
v___x_2632_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2641_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2641_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2641_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2637_ = l_Lean_Expr_app___override(v_a_2633_, v_n_2626_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2637_);
v___x_2639_ = v___x_2635_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
else
{
lean_dec_ref(v_n_2626_);
return v___x_2632_;
}
}
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec_ref(v___x_2602_);
lean_dec_ref(v_n_2599_);
lean_dec_ref(v_semiringInst_2597_);
lean_dec_ref(v_type_2595_);
v_a_2647_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2606_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2606_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
v_a_2655_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2592_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2592_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(lean_object* v_k_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec(v_k_2663_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(lean_object* v_a_2677_, lean_object* v_s_2678_){
_start:
{
lean_object* v_toRing_2679_; lean_object* v_invFn_x3f_2680_; lean_object* v_semiringId_x3f_2681_; lean_object* v_commSemiringInst_2682_; lean_object* v_commRingInst_2683_; lean_object* v_noZeroDivInst_x3f_2684_; lean_object* v_fieldInst_x3f_2685_; lean_object* v_denoteEntries_2686_; lean_object* v_nextId_2687_; lean_object* v_steps_2688_; lean_object* v_queue_2689_; lean_object* v_basis_2690_; lean_object* v_diseqs_2691_; uint8_t v_recheck_2692_; lean_object* v_invSet_2693_; lean_object* v_numEq0_x3f_2694_; uint8_t v_numEq0Updated_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2727_; 
v_toRing_2679_ = lean_ctor_get(v_s_2678_, 0);
v_invFn_x3f_2680_ = lean_ctor_get(v_s_2678_, 1);
v_semiringId_x3f_2681_ = lean_ctor_get(v_s_2678_, 2);
v_commSemiringInst_2682_ = lean_ctor_get(v_s_2678_, 3);
v_commRingInst_2683_ = lean_ctor_get(v_s_2678_, 4);
v_noZeroDivInst_x3f_2684_ = lean_ctor_get(v_s_2678_, 5);
v_fieldInst_x3f_2685_ = lean_ctor_get(v_s_2678_, 6);
v_denoteEntries_2686_ = lean_ctor_get(v_s_2678_, 7);
v_nextId_2687_ = lean_ctor_get(v_s_2678_, 8);
v_steps_2688_ = lean_ctor_get(v_s_2678_, 9);
v_queue_2689_ = lean_ctor_get(v_s_2678_, 10);
v_basis_2690_ = lean_ctor_get(v_s_2678_, 11);
v_diseqs_2691_ = lean_ctor_get(v_s_2678_, 12);
v_recheck_2692_ = lean_ctor_get_uint8(v_s_2678_, sizeof(void*)*15);
v_invSet_2693_ = lean_ctor_get(v_s_2678_, 13);
v_numEq0_x3f_2694_ = lean_ctor_get(v_s_2678_, 14);
v_numEq0Updated_2695_ = lean_ctor_get_uint8(v_s_2678_, sizeof(void*)*15 + 1);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_s_2678_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2697_ = v_s_2678_;
v_isShared_2698_ = v_isSharedCheck_2727_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_numEq0_x3f_2694_);
lean_inc(v_invSet_2693_);
lean_inc(v_diseqs_2691_);
lean_inc(v_basis_2690_);
lean_inc(v_queue_2689_);
lean_inc(v_steps_2688_);
lean_inc(v_nextId_2687_);
lean_inc(v_denoteEntries_2686_);
lean_inc(v_fieldInst_x3f_2685_);
lean_inc(v_noZeroDivInst_x3f_2684_);
lean_inc(v_commRingInst_2683_);
lean_inc(v_commSemiringInst_2682_);
lean_inc(v_semiringId_x3f_2681_);
lean_inc(v_invFn_x3f_2680_);
lean_inc(v_toRing_2679_);
lean_dec(v_s_2678_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2727_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v_id_2699_; lean_object* v_type_2700_; lean_object* v_u_2701_; lean_object* v_ringInst_2702_; lean_object* v_semiringInst_2703_; lean_object* v_charInst_x3f_2704_; lean_object* v_addFn_x3f_2705_; lean_object* v_mulFn_x3f_2706_; lean_object* v_subFn_x3f_2707_; lean_object* v_negFn_x3f_2708_; lean_object* v_intCastFn_x3f_2709_; lean_object* v_natCastFn_x3f_2710_; lean_object* v_one_x3f_2711_; lean_object* v_vars_2712_; lean_object* v_varMap_2713_; lean_object* v_denote_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2725_; 
v_id_2699_ = lean_ctor_get(v_toRing_2679_, 0);
v_type_2700_ = lean_ctor_get(v_toRing_2679_, 1);
v_u_2701_ = lean_ctor_get(v_toRing_2679_, 2);
v_ringInst_2702_ = lean_ctor_get(v_toRing_2679_, 3);
v_semiringInst_2703_ = lean_ctor_get(v_toRing_2679_, 4);
v_charInst_x3f_2704_ = lean_ctor_get(v_toRing_2679_, 5);
v_addFn_x3f_2705_ = lean_ctor_get(v_toRing_2679_, 6);
v_mulFn_x3f_2706_ = lean_ctor_get(v_toRing_2679_, 7);
v_subFn_x3f_2707_ = lean_ctor_get(v_toRing_2679_, 8);
v_negFn_x3f_2708_ = lean_ctor_get(v_toRing_2679_, 9);
v_intCastFn_x3f_2709_ = lean_ctor_get(v_toRing_2679_, 11);
v_natCastFn_x3f_2710_ = lean_ctor_get(v_toRing_2679_, 12);
v_one_x3f_2711_ = lean_ctor_get(v_toRing_2679_, 13);
v_vars_2712_ = lean_ctor_get(v_toRing_2679_, 14);
v_varMap_2713_ = lean_ctor_get(v_toRing_2679_, 15);
v_denote_2714_ = lean_ctor_get(v_toRing_2679_, 16);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_toRing_2679_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v_toRing_2679_, 10);
lean_dec(v_unused_2726_);
v___x_2716_ = v_toRing_2679_;
v_isShared_2717_ = v_isSharedCheck_2725_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_denote_2714_);
lean_inc(v_varMap_2713_);
lean_inc(v_vars_2712_);
lean_inc(v_one_x3f_2711_);
lean_inc(v_natCastFn_x3f_2710_);
lean_inc(v_intCastFn_x3f_2709_);
lean_inc(v_negFn_x3f_2708_);
lean_inc(v_subFn_x3f_2707_);
lean_inc(v_mulFn_x3f_2706_);
lean_inc(v_addFn_x3f_2705_);
lean_inc(v_charInst_x3f_2704_);
lean_inc(v_semiringInst_2703_);
lean_inc(v_ringInst_2702_);
lean_inc(v_u_2701_);
lean_inc(v_type_2700_);
lean_inc(v_id_2699_);
lean_dec(v_toRing_2679_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2725_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2718_, 0, v_a_2677_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 10, v___x_2718_);
v___x_2720_ = v___x_2716_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_id_2699_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_type_2700_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v_u_2701_);
lean_ctor_set(v_reuseFailAlloc_2724_, 3, v_ringInst_2702_);
lean_ctor_set(v_reuseFailAlloc_2724_, 4, v_semiringInst_2703_);
lean_ctor_set(v_reuseFailAlloc_2724_, 5, v_charInst_x3f_2704_);
lean_ctor_set(v_reuseFailAlloc_2724_, 6, v_addFn_x3f_2705_);
lean_ctor_set(v_reuseFailAlloc_2724_, 7, v_mulFn_x3f_2706_);
lean_ctor_set(v_reuseFailAlloc_2724_, 8, v_subFn_x3f_2707_);
lean_ctor_set(v_reuseFailAlloc_2724_, 9, v_negFn_x3f_2708_);
lean_ctor_set(v_reuseFailAlloc_2724_, 10, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2724_, 11, v_intCastFn_x3f_2709_);
lean_ctor_set(v_reuseFailAlloc_2724_, 12, v_natCastFn_x3f_2710_);
lean_ctor_set(v_reuseFailAlloc_2724_, 13, v_one_x3f_2711_);
lean_ctor_set(v_reuseFailAlloc_2724_, 14, v_vars_2712_);
lean_ctor_set(v_reuseFailAlloc_2724_, 15, v_varMap_2713_);
lean_ctor_set(v_reuseFailAlloc_2724_, 16, v_denote_2714_);
v___x_2720_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2722_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2720_);
v___x_2722_ = v___x_2697_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v_invFn_x3f_2680_);
lean_ctor_set(v_reuseFailAlloc_2723_, 2, v_semiringId_x3f_2681_);
lean_ctor_set(v_reuseFailAlloc_2723_, 3, v_commSemiringInst_2682_);
lean_ctor_set(v_reuseFailAlloc_2723_, 4, v_commRingInst_2683_);
lean_ctor_set(v_reuseFailAlloc_2723_, 5, v_noZeroDivInst_x3f_2684_);
lean_ctor_set(v_reuseFailAlloc_2723_, 6, v_fieldInst_x3f_2685_);
lean_ctor_set(v_reuseFailAlloc_2723_, 7, v_denoteEntries_2686_);
lean_ctor_set(v_reuseFailAlloc_2723_, 8, v_nextId_2687_);
lean_ctor_set(v_reuseFailAlloc_2723_, 9, v_steps_2688_);
lean_ctor_set(v_reuseFailAlloc_2723_, 10, v_queue_2689_);
lean_ctor_set(v_reuseFailAlloc_2723_, 11, v_basis_2690_);
lean_ctor_set(v_reuseFailAlloc_2723_, 12, v_diseqs_2691_);
lean_ctor_set(v_reuseFailAlloc_2723_, 13, v_invSet_2693_);
lean_ctor_set(v_reuseFailAlloc_2723_, 14, v_numEq0_x3f_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, sizeof(void*)*15, v_recheck_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, sizeof(void*)*15 + 1, v_numEq0Updated_2695_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = l_Lean_Level_ofNat(v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(lean_object* v_u_2743_, lean_object* v_type_2744_, lean_object* v_semiringInst_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2758_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1));
v___x_2759_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2);
v___x_2760_ = lean_box(0);
lean_inc(v_u_2743_);
v___x_2761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2761_, 0, v_u_2743_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
lean_inc_ref(v___x_2761_);
v___x_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2759_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2763_, 0, v_u_2743_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
lean_inc_ref(v___x_2763_);
v___x_2764_ = l_Lean_mkConst(v___x_2758_, v___x_2763_);
v___x_2765_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2744_, 2);
v___x_2766_ = l_Lean_mkApp3(v___x_2764_, v_type_2744_, v___x_2765_, v_type_2744_);
v___x_2767_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2766_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v_inst_x27_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc_n(v_a_2768_, 2);
lean_dec_ref(v___x_2767_);
v___x_2769_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4));
v___x_2770_ = l_Lean_mkConst(v___x_2769_, v___x_2761_);
lean_inc_ref(v_type_2744_);
v_inst_x27_2771_ = l_Lean_mkAppB(v___x_2770_, v_type_2744_, v_semiringInst_2745_);
v___x_2772_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6));
v___x_2773_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_2772_, v_a_2768_, v_inst_x27_2771_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
lean_dec_ref(v___x_2773_);
v___x_2774_ = l_Lean_mkConst(v___x_2772_, v___x_2763_);
lean_inc_ref(v_type_2744_);
v___x_2775_ = l_Lean_mkApp4(v___x_2774_, v_type_2744_, v___x_2765_, v_type_2744_, v_a_2768_);
v___x_2776_ = l_Lean_Meta_Sym_canon(v___x_2775_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref(v___x_2776_);
v___x_2778_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2777_, v___y_2752_);
return v___x_2778_;
}
else
{
return v___x_2776_;
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_a_2768_);
lean_dec_ref(v___x_2763_);
lean_dec_ref(v_type_2744_);
v_a_2779_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2773_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2773_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
else
{
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2761_);
lean_dec_ref(v_semiringInst_2745_);
lean_dec_ref(v_type_2744_);
return v___x_2767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___boxed(lean_object* v_u_2787_, lean_object* v_type_2788_, lean_object* v_semiringInst_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2787_, v_type_2788_, v_semiringInst_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec(v___y_2790_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2849_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2849_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2849_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_toRing_2820_; lean_object* v_powFn_x3f_2821_; 
v_toRing_2820_ = lean_ctor_get(v_a_2816_, 0);
lean_inc_ref(v_toRing_2820_);
lean_dec(v_a_2816_);
v_powFn_x3f_2821_ = lean_ctor_get(v_toRing_2820_, 10);
if (lean_obj_tag(v_powFn_x3f_2821_) == 1)
{
lean_object* v_val_2822_; lean_object* v___x_2824_; 
lean_inc_ref(v_powFn_x3f_2821_);
lean_dec_ref(v_toRing_2820_);
v_val_2822_ = lean_ctor_get(v_powFn_x3f_2821_, 0);
lean_inc(v_val_2822_);
lean_dec_ref(v_powFn_x3f_2821_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v_val_2822_);
v___x_2824_ = v___x_2818_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_val_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
else
{
lean_object* v_type_2826_; lean_object* v_u_2827_; lean_object* v_semiringInst_2828_; lean_object* v___x_2829_; 
lean_del_object(v___x_2818_);
v_type_2826_ = lean_ctor_get(v_toRing_2820_, 1);
lean_inc_ref(v_type_2826_);
v_u_2827_ = lean_ctor_get(v_toRing_2820_, 2);
lean_inc(v_u_2827_);
v_semiringInst_2828_ = lean_ctor_get(v_toRing_2820_, 4);
lean_inc_ref(v_semiringInst_2828_);
lean_dec_ref(v_toRing_2820_);
v___x_2829_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2827_, v_type_2826_, v_semiringInst_2828_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___f_2831_; lean_object* v___x_2832_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc_n(v_a_2830_, 2);
lean_dec_ref(v___x_2829_);
v___f_2831_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_2831_, 0, v_a_2830_);
v___x_2832_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2831_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2839_ == 0)
{
lean_object* v_unused_2840_; 
v_unused_2840_ = lean_ctor_get(v___x_2832_, 0);
lean_dec(v_unused_2840_);
v___x_2834_ = v___x_2832_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_dec(v___x_2832_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v_a_2830_);
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2830_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec(v_a_2830_);
v_a_2841_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2832_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2832_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
else
{
return v___x_2829_;
}
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
v_a_2850_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2815_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2815_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec(v___y_2858_);
return v_res_2870_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2));
v___x_2875_ = lean_unsigned_to_nat(39u);
v___x_2876_ = lean_unsigned_to_nat(159u);
v___x_2877_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1));
v___x_2878_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0));
v___x_2879_ = l_mkPanicMessageWithDecl(v___x_2878_, v___x_2877_, v___x_2876_, v___x_2875_, v___x_2874_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
switch(lean_obj_tag(v_a_2880_))
{
case 0:
{
lean_object* v_k_2893_; lean_object* v___x_2894_; 
v_k_2893_ = lean_ctor_get(v_a_2880_, 0);
lean_inc(v_k_2893_);
lean_dec_ref(v_a_2880_);
v___x_2894_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2893_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
lean_dec(v_k_2893_);
return v___x_2894_;
}
case 1:
{
lean_object* v_k_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_k_2895_ = lean_ctor_get(v_a_2880_, 0);
lean_inc(v_k_2895_);
lean_dec_ref(v_a_2880_);
v___x_2896_ = lean_nat_to_int(v_k_2895_);
v___x_2897_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v___x_2896_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
lean_dec(v___x_2896_);
return v___x_2897_;
}
case 3:
{
lean_object* v_i_2898_; lean_object* v___x_2899_; 
v_i_2898_ = lean_ctor_get(v_a_2880_, 0);
lean_inc(v_i_2898_);
lean_dec_ref(v_a_2880_);
v___x_2899_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref(v___x_2899_);
v___x_2901_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2919_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2904_ = v___x_2901_;
v_isShared_2905_ = v_isSharedCheck_2919_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2901_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2919_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___y_2907_; lean_object* v_toSemiring_2912_; lean_object* v_vars_2913_; lean_object* v_size_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
v_toSemiring_2912_ = lean_ctor_get(v_a_2902_, 0);
lean_inc_ref(v_toSemiring_2912_);
lean_dec(v_a_2902_);
v_vars_2913_ = lean_ctor_get(v_toSemiring_2912_, 9);
lean_inc_ref(v_vars_2913_);
lean_dec_ref(v_toSemiring_2912_);
v_size_2914_ = lean_ctor_get(v_vars_2913_, 2);
v___x_2915_ = l_Lean_instInhabitedExpr;
v___x_2916_ = lean_nat_dec_lt(v_i_2898_, v_size_2914_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; 
lean_dec_ref(v_vars_2913_);
lean_dec(v_i_2898_);
v___x_2917_ = l_outOfBounds___redArg(v___x_2915_);
v___y_2907_ = v___x_2917_;
goto v___jp_2906_;
}
else
{
lean_object* v___x_2918_; 
v___x_2918_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2915_, v_vars_2913_, v_i_2898_);
lean_dec(v_i_2898_);
lean_dec_ref(v_vars_2913_);
v___y_2907_ = v___x_2918_;
goto v___jp_2906_;
}
v___jp_2906_:
{
lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2908_ = l_Lean_Expr_app___override(v_a_2900_, v___y_2907_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 0, v___x_2908_);
v___x_2910_ = v___x_2904_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_a_2900_);
lean_dec(v_i_2898_);
v_a_2920_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2901_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2901_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
else
{
lean_dec(v_i_2898_);
return v___x_2899_;
}
}
case 5:
{
lean_object* v_a_2928_; lean_object* v_b_2929_; lean_object* v___x_2930_; 
v_a_2928_ = lean_ctor_get(v_a_2880_, 0);
lean_inc_ref(v_a_2928_);
v_b_2929_ = lean_ctor_get(v_a_2880_, 1);
lean_inc_ref(v_b_2929_);
lean_dec_ref(v_a_2880_);
v___x_2930_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2932_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref(v___x_2930_);
v___x_2932_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2928_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2934_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref(v___x_2932_);
v___x_2934_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2929_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2943_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2937_ = v___x_2934_;
v_isShared_2938_ = v_isSharedCheck_2943_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2943_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
v___x_2939_ = l_Lean_mkAppB(v_a_2931_, v_a_2933_, v_a_2935_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 0, v___x_2939_);
v___x_2941_ = v___x_2937_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
else
{
lean_dec(v_a_2933_);
lean_dec(v_a_2931_);
return v___x_2934_;
}
}
else
{
lean_dec(v_a_2931_);
lean_dec_ref(v_b_2929_);
return v___x_2932_;
}
}
else
{
lean_dec_ref(v_b_2929_);
lean_dec_ref(v_a_2928_);
return v___x_2930_;
}
}
case 7:
{
lean_object* v_a_2944_; lean_object* v_b_2945_; lean_object* v___x_2946_; 
v_a_2944_ = lean_ctor_get(v_a_2880_, 0);
lean_inc_ref(v_a_2944_);
v_b_2945_ = lean_ctor_get(v_a_2880_, 1);
lean_inc_ref(v_b_2945_);
lean_dec_ref(v_a_2880_);
v___x_2946_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2948_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref(v___x_2946_);
v___x_2948_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2944_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2950_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref(v___x_2948_);
v___x_2950_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2945_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2959_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2953_ = v___x_2950_;
v_isShared_2954_ = v_isSharedCheck_2959_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2950_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2959_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2957_; 
v___x_2955_ = l_Lean_mkAppB(v_a_2947_, v_a_2949_, v_a_2951_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 0, v___x_2955_);
v___x_2957_ = v___x_2953_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
else
{
lean_dec(v_a_2949_);
lean_dec(v_a_2947_);
return v___x_2950_;
}
}
else
{
lean_dec(v_a_2947_);
lean_dec_ref(v_b_2945_);
return v___x_2948_;
}
}
else
{
lean_dec_ref(v_b_2945_);
lean_dec_ref(v_a_2944_);
return v___x_2946_;
}
}
case 8:
{
lean_object* v_a_2960_; lean_object* v_k_2961_; lean_object* v___x_2962_; 
v_a_2960_ = lean_ctor_get(v_a_2880_, 0);
lean_inc_ref(v_a_2960_);
v_k_2961_ = lean_ctor_get(v_a_2880_, 1);
lean_inc(v_k_2961_);
lean_dec_ref(v_a_2880_);
v___x_2962_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2964_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref(v___x_2962_);
v___x_2964_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2960_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2974_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2967_ = v___x_2964_;
v_isShared_2968_ = v_isSharedCheck_2974_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2974_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2969_ = l_Lean_mkNatLit(v_k_2961_);
v___x_2970_ = l_Lean_mkAppB(v_a_2963_, v_a_2965_, v___x_2969_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 0, v___x_2970_);
v___x_2972_ = v___x_2967_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
else
{
lean_dec(v_a_2963_);
lean_dec(v_k_2961_);
return v___x_2964_;
}
}
else
{
lean_dec(v_k_2961_);
lean_dec_ref(v_a_2960_);
return v___x_2962_;
}
}
default: 
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
lean_dec_ref(v_a_2880_);
v___x_2975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3);
v___x_2976_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___x_2975_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
return v___x_2976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec(v_a_2979_);
lean_dec(v_a_2978_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(lean_object* v_type_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_2991_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___boxed(lean_object* v_type_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(v_type_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
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
lean_dec(v___y_3006_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object* v_e_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_e_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3034_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref(v___x_3032_);
v___x_3034_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3033_, v_a_3026_);
return v___x_3034_;
}
else
{
return v___x_3032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object* v_e_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(v_e_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
lean_dec(v_a_3042_);
lean_dec_ref(v_a_3041_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
lean_dec(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec(v_a_3036_);
return v_res_3048_;
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
