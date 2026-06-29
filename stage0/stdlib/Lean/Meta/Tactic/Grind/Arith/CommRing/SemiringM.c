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
size_t lean_usize_sub(size_t, size_t);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_104_, 1);
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
lean_object* v_rings_285_; lean_object* v_typeIdOf_286_; lean_object* v_exprToRingId_287_; lean_object* v_semirings_288_; lean_object* v_stypeIdOf_289_; lean_object* v_exprToSemiringId_290_; lean_object* v_ncRings_291_; lean_object* v_exprToNCRingId_292_; lean_object* v_nctypeIdOf_293_; lean_object* v_ncSemirings_294_; lean_object* v_exprToNCSemiringId_295_; lean_object* v_ncstypeIdOf_296_; lean_object* v_steps_297_; uint8_t v_reportedMaxDegreeIssue_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
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
v_reportedMaxDegreeIssue_298_ = lean_ctor_get_uint8(v_s_284_, sizeof(void*)*13);
v___x_299_ = lean_array_get_size(v_semirings_288_);
v___x_300_ = lean_nat_dec_lt(v_a_282_, v___x_299_);
if (v___x_300_ == 0)
{
lean_dec_ref(v_f_283_);
return v_s_284_;
}
else
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_312_; 
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
v_isSharedCheck_312_ = !lean_is_exclusive(v_s_284_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; lean_object* v_unused_319_; lean_object* v_unused_320_; lean_object* v_unused_321_; lean_object* v_unused_322_; lean_object* v_unused_323_; lean_object* v_unused_324_; lean_object* v_unused_325_; 
v_unused_313_ = lean_ctor_get(v_s_284_, 12);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_s_284_, 11);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_s_284_, 10);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_s_284_, 9);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_s_284_, 8);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_s_284_, 7);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_s_284_, 6);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_s_284_, 5);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_s_284_, 4);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_s_284_, 3);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_s_284_, 2);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_s_284_, 1);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_s_284_, 0);
lean_dec(v_unused_325_);
v___x_302_ = v_s_284_;
v_isShared_303_ = v_isSharedCheck_312_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_s_284_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_312_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_v_304_; lean_object* v___x_305_; lean_object* v_xs_x27_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v_v_304_ = lean_array_fget(v_semirings_288_, v_a_282_);
v___x_305_ = lean_box(0);
v_xs_x27_306_ = lean_array_fset(v_semirings_288_, v_a_282_, v___x_305_);
v___x_307_ = lean_apply_1(v_f_283_, v_v_304_);
v___x_308_ = lean_array_fset(v_xs_x27_306_, v_a_282_, v___x_307_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 3, v___x_308_);
v___x_310_ = v___x_302_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_rings_285_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_typeIdOf_286_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_exprToRingId_287_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v_stypeIdOf_289_);
lean_ctor_set(v_reuseFailAlloc_311_, 5, v_exprToSemiringId_290_);
lean_ctor_set(v_reuseFailAlloc_311_, 6, v_ncRings_291_);
lean_ctor_set(v_reuseFailAlloc_311_, 7, v_exprToNCRingId_292_);
lean_ctor_set(v_reuseFailAlloc_311_, 8, v_nctypeIdOf_293_);
lean_ctor_set(v_reuseFailAlloc_311_, 9, v_ncSemirings_294_);
lean_ctor_set(v_reuseFailAlloc_311_, 10, v_exprToNCSemiringId_295_);
lean_ctor_set(v_reuseFailAlloc_311_, 11, v_ncstypeIdOf_296_);
lean_ctor_set(v_reuseFailAlloc_311_, 12, v_steps_297_);
lean_ctor_set_uint8(v_reuseFailAlloc_311_, sizeof(void*)*13, v_reportedMaxDegreeIssue_298_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed(lean_object* v_a_326_, lean_object* v_f_327_, lean_object* v_s_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(v_a_326_, v_f_327_, v_s_328_);
lean_dec(v_a_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(lean_object* v_f_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___f_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
lean_inc(v_a_331_);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_334_, 0, v_a_331_);
lean_closure_set(v___f_334_, 1, v_f_330_);
v___x_335_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_336_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_335_, v___f_334_, v_a_332_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___boxed(lean_object* v_f_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(v_f_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec(v_a_338_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(lean_object* v_f_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___f_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
lean_inc(v_a_343_);
v___f_355_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_355_, 0, v_a_343_);
lean_closure_set(v___f_355_, 1, v_f_342_);
v___x_356_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_357_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_356_, v___f_355_, v_a_344_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed(lean_object* v_f_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(v_f_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec(v_a_360_);
lean_dec(v_a_359_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0));
v___x_374_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed), 12, 0);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM(void){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0));
v___x_379_ = l_Lean_stringToMessageData(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_381_, v_a_389_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_394_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v___x_392_, 1);
v___x_394_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_409_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_409_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_409_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_409_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_ringId_399_; lean_object* v_rings_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_ringId_399_ = lean_ctor_get(v_a_395_, 1);
lean_inc(v_ringId_399_);
lean_dec(v_a_395_);
v_rings_400_ = lean_ctor_get(v_a_393_, 0);
lean_inc_ref(v_rings_400_);
lean_dec(v_a_393_);
v___x_401_ = lean_array_get_size(v_rings_400_);
v___x_402_ = lean_nat_dec_lt(v_ringId_399_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec_ref(v_rings_400_);
lean_dec(v_ringId_399_);
lean_del_object(v___x_397_);
v___x_403_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1);
v___x_404_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_403_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
return v___x_404_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_array_fget(v_rings_400_, v_ringId_399_);
lean_dec(v_ringId_399_);
lean_dec_ref(v_rings_400_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_405_);
v___x_407_ = v___x_397_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_a_393_);
v_a_410_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_394_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_394_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
v_a_418_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_392_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_392_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed(lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec(v_a_427_);
lean_dec(v_a_426_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(lean_object* v_ringId_439_, lean_object* v_f_440_, lean_object* v_s_441_){
_start:
{
lean_object* v_rings_442_; lean_object* v_typeIdOf_443_; lean_object* v_exprToRingId_444_; lean_object* v_semirings_445_; lean_object* v_stypeIdOf_446_; lean_object* v_exprToSemiringId_447_; lean_object* v_ncRings_448_; lean_object* v_exprToNCRingId_449_; lean_object* v_nctypeIdOf_450_; lean_object* v_ncSemirings_451_; lean_object* v_exprToNCSemiringId_452_; lean_object* v_ncstypeIdOf_453_; lean_object* v_steps_454_; uint8_t v_reportedMaxDegreeIssue_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v_rings_442_ = lean_ctor_get(v_s_441_, 0);
v_typeIdOf_443_ = lean_ctor_get(v_s_441_, 1);
v_exprToRingId_444_ = lean_ctor_get(v_s_441_, 2);
v_semirings_445_ = lean_ctor_get(v_s_441_, 3);
v_stypeIdOf_446_ = lean_ctor_get(v_s_441_, 4);
v_exprToSemiringId_447_ = lean_ctor_get(v_s_441_, 5);
v_ncRings_448_ = lean_ctor_get(v_s_441_, 6);
v_exprToNCRingId_449_ = lean_ctor_get(v_s_441_, 7);
v_nctypeIdOf_450_ = lean_ctor_get(v_s_441_, 8);
v_ncSemirings_451_ = lean_ctor_get(v_s_441_, 9);
v_exprToNCSemiringId_452_ = lean_ctor_get(v_s_441_, 10);
v_ncstypeIdOf_453_ = lean_ctor_get(v_s_441_, 11);
v_steps_454_ = lean_ctor_get(v_s_441_, 12);
v_reportedMaxDegreeIssue_455_ = lean_ctor_get_uint8(v_s_441_, sizeof(void*)*13);
v___x_456_ = lean_array_get_size(v_rings_442_);
v___x_457_ = lean_nat_dec_lt(v_ringId_439_, v___x_456_);
if (v___x_457_ == 0)
{
lean_dec_ref(v_f_440_);
return v_s_441_;
}
else
{
lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_469_; 
lean_inc(v_steps_454_);
lean_inc_ref(v_ncstypeIdOf_453_);
lean_inc_ref(v_exprToNCSemiringId_452_);
lean_inc_ref(v_ncSemirings_451_);
lean_inc_ref(v_nctypeIdOf_450_);
lean_inc_ref(v_exprToNCRingId_449_);
lean_inc_ref(v_ncRings_448_);
lean_inc_ref(v_exprToSemiringId_447_);
lean_inc_ref(v_stypeIdOf_446_);
lean_inc_ref(v_semirings_445_);
lean_inc_ref(v_exprToRingId_444_);
lean_inc_ref(v_typeIdOf_443_);
lean_inc_ref(v_rings_442_);
v_isSharedCheck_469_ = !lean_is_exclusive(v_s_441_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; lean_object* v_unused_479_; lean_object* v_unused_480_; lean_object* v_unused_481_; lean_object* v_unused_482_; 
v_unused_470_ = lean_ctor_get(v_s_441_, 12);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_s_441_, 11);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_s_441_, 10);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_s_441_, 9);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_s_441_, 8);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_s_441_, 7);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_s_441_, 6);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_s_441_, 5);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_s_441_, 4);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_s_441_, 3);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_s_441_, 2);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_s_441_, 1);
lean_dec(v_unused_481_);
v_unused_482_ = lean_ctor_get(v_s_441_, 0);
lean_dec(v_unused_482_);
v___x_459_ = v_s_441_;
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
else
{
lean_dec(v_s_441_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_v_461_; lean_object* v___x_462_; lean_object* v_xs_x27_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v_v_461_ = lean_array_fget(v_rings_442_, v_ringId_439_);
v___x_462_ = lean_box(0);
v_xs_x27_463_ = lean_array_fset(v_rings_442_, v_ringId_439_, v___x_462_);
v___x_464_ = lean_apply_1(v_f_440_, v_v_461_);
v___x_465_ = lean_array_fset(v_xs_x27_463_, v_ringId_439_, v___x_464_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_465_);
v___x_467_ = v___x_459_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_typeIdOf_443_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_exprToRingId_444_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_semirings_445_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_stypeIdOf_446_);
lean_ctor_set(v_reuseFailAlloc_468_, 5, v_exprToSemiringId_447_);
lean_ctor_set(v_reuseFailAlloc_468_, 6, v_ncRings_448_);
lean_ctor_set(v_reuseFailAlloc_468_, 7, v_exprToNCRingId_449_);
lean_ctor_set(v_reuseFailAlloc_468_, 8, v_nctypeIdOf_450_);
lean_ctor_set(v_reuseFailAlloc_468_, 9, v_ncSemirings_451_);
lean_ctor_set(v_reuseFailAlloc_468_, 10, v_exprToNCSemiringId_452_);
lean_ctor_set(v_reuseFailAlloc_468_, 11, v_ncstypeIdOf_453_);
lean_ctor_set(v_reuseFailAlloc_468_, 12, v_steps_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_468_, sizeof(void*)*13, v_reportedMaxDegreeIssue_455_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed(lean_object* v_ringId_483_, lean_object* v_f_484_, lean_object* v_s_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(v_ringId_483_, v_f_484_, v_s_485_);
lean_dec(v_ringId_483_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(lean_object* v_f_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v_ringId_502_; lean_object* v___f_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v_ringId_502_ = lean_ctor_get(v_a_501_, 1);
lean_inc(v_ringId_502_);
lean_dec(v_a_501_);
v___f_503_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed), 3, 2);
lean_closure_set(v___f_503_, 0, v_ringId_502_);
lean_closure_set(v___f_503_, 1, v_f_487_);
v___x_504_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_505_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_504_, v___f_503_, v_a_489_);
return v___x_505_;
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec_ref(v_f_487_);
v_a_506_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_500_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_500_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed(lean_object* v_f_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v_f_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec(v_a_516_);
lean_dec(v_a_515_);
return v_res_527_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0));
v___x_530_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed), 12, 0);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM(void){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0(lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_s_535_){
_start:
{
lean_object* v_rings_536_; lean_object* v_typeIdOf_537_; lean_object* v_exprToRingId_538_; lean_object* v_semirings_539_; lean_object* v_stypeIdOf_540_; lean_object* v_exprToSemiringId_541_; lean_object* v_ncRings_542_; lean_object* v_exprToNCRingId_543_; lean_object* v_nctypeIdOf_544_; lean_object* v_ncSemirings_545_; lean_object* v_exprToNCSemiringId_546_; lean_object* v_ncstypeIdOf_547_; lean_object* v_steps_548_; uint8_t v_reportedMaxDegreeIssue_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_rings_536_ = lean_ctor_get(v_s_535_, 0);
v_typeIdOf_537_ = lean_ctor_get(v_s_535_, 1);
v_exprToRingId_538_ = lean_ctor_get(v_s_535_, 2);
v_semirings_539_ = lean_ctor_get(v_s_535_, 3);
v_stypeIdOf_540_ = lean_ctor_get(v_s_535_, 4);
v_exprToSemiringId_541_ = lean_ctor_get(v_s_535_, 5);
v_ncRings_542_ = lean_ctor_get(v_s_535_, 6);
v_exprToNCRingId_543_ = lean_ctor_get(v_s_535_, 7);
v_nctypeIdOf_544_ = lean_ctor_get(v_s_535_, 8);
v_ncSemirings_545_ = lean_ctor_get(v_s_535_, 9);
v_exprToNCSemiringId_546_ = lean_ctor_get(v_s_535_, 10);
v_ncstypeIdOf_547_ = lean_ctor_get(v_s_535_, 11);
v_steps_548_ = lean_ctor_get(v_s_535_, 12);
v_reportedMaxDegreeIssue_549_ = lean_ctor_get_uint8(v_s_535_, sizeof(void*)*13);
v___x_550_ = lean_array_get_size(v_semirings_539_);
v___x_551_ = lean_nat_dec_lt(v_a_533_, v___x_550_);
if (v___x_551_ == 0)
{
lean_dec_ref(v_a_534_);
return v_s_535_;
}
else
{
lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_575_; 
lean_inc(v_steps_548_);
lean_inc_ref(v_ncstypeIdOf_547_);
lean_inc_ref(v_exprToNCSemiringId_546_);
lean_inc_ref(v_ncSemirings_545_);
lean_inc_ref(v_nctypeIdOf_544_);
lean_inc_ref(v_exprToNCRingId_543_);
lean_inc_ref(v_ncRings_542_);
lean_inc_ref(v_exprToSemiringId_541_);
lean_inc_ref(v_stypeIdOf_540_);
lean_inc_ref(v_semirings_539_);
lean_inc_ref(v_exprToRingId_538_);
lean_inc_ref(v_typeIdOf_537_);
lean_inc_ref(v_rings_536_);
v_isSharedCheck_575_ = !lean_is_exclusive(v_s_535_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; lean_object* v_unused_577_; lean_object* v_unused_578_; lean_object* v_unused_579_; lean_object* v_unused_580_; lean_object* v_unused_581_; lean_object* v_unused_582_; lean_object* v_unused_583_; lean_object* v_unused_584_; lean_object* v_unused_585_; lean_object* v_unused_586_; lean_object* v_unused_587_; lean_object* v_unused_588_; 
v_unused_576_ = lean_ctor_get(v_s_535_, 12);
lean_dec(v_unused_576_);
v_unused_577_ = lean_ctor_get(v_s_535_, 11);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_s_535_, 10);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_s_535_, 9);
lean_dec(v_unused_579_);
v_unused_580_ = lean_ctor_get(v_s_535_, 8);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_s_535_, 7);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_s_535_, 6);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_s_535_, 5);
lean_dec(v_unused_583_);
v_unused_584_ = lean_ctor_get(v_s_535_, 4);
lean_dec(v_unused_584_);
v_unused_585_ = lean_ctor_get(v_s_535_, 3);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_s_535_, 2);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_s_535_, 1);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_s_535_, 0);
lean_dec(v_unused_588_);
v___x_553_ = v_s_535_;
v_isShared_554_ = v_isSharedCheck_575_;
goto v_resetjp_552_;
}
else
{
lean_dec(v_s_535_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_575_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_v_555_; lean_object* v_toSemiring_556_; lean_object* v_ringId_557_; lean_object* v_commSemiringInst_558_; lean_object* v_addRightCancelInst_x3f_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_573_; 
v_v_555_ = lean_array_fget(v_semirings_539_, v_a_533_);
v_toSemiring_556_ = lean_ctor_get(v_v_555_, 0);
v_ringId_557_ = lean_ctor_get(v_v_555_, 1);
v_commSemiringInst_558_ = lean_ctor_get(v_v_555_, 2);
v_addRightCancelInst_x3f_559_ = lean_ctor_get(v_v_555_, 3);
v_isSharedCheck_573_ = !lean_is_exclusive(v_v_555_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v_v_555_, 4);
lean_dec(v_unused_574_);
v___x_561_ = v_v_555_;
v_isShared_562_ = v_isSharedCheck_573_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_addRightCancelInst_x3f_559_);
lean_inc(v_commSemiringInst_558_);
lean_inc(v_ringId_557_);
lean_inc(v_toSemiring_556_);
lean_dec(v_v_555_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_573_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v_xs_x27_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_563_ = lean_box(0);
v_xs_x27_564_ = lean_array_fset(v_semirings_539_, v_a_533_, v___x_563_);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v_a_534_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 4, v___x_565_);
v___x_567_ = v___x_561_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_toSemiring_556_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_ringId_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_commSemiringInst_558_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_addRightCancelInst_x3f_559_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v___x_565_);
v___x_567_ = v_reuseFailAlloc_572_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = lean_array_fset(v_xs_x27_564_, v_a_533_, v___x_567_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 3, v___x_568_);
v___x_570_ = v___x_553_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_rings_536_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_typeIdOf_537_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_exprToRingId_538_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v_stypeIdOf_540_);
lean_ctor_set(v_reuseFailAlloc_571_, 5, v_exprToSemiringId_541_);
lean_ctor_set(v_reuseFailAlloc_571_, 6, v_ncRings_542_);
lean_ctor_set(v_reuseFailAlloc_571_, 7, v_exprToNCRingId_543_);
lean_ctor_set(v_reuseFailAlloc_571_, 8, v_nctypeIdOf_544_);
lean_ctor_set(v_reuseFailAlloc_571_, 9, v_ncSemirings_545_);
lean_ctor_set(v_reuseFailAlloc_571_, 10, v_exprToNCSemiringId_546_);
lean_ctor_set(v_reuseFailAlloc_571_, 11, v_ncstypeIdOf_547_);
lean_ctor_set(v_reuseFailAlloc_571_, 12, v_steps_548_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, sizeof(void*)*13, v_reportedMaxDegreeIssue_549_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0___boxed(lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_s_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0(v_a_589_, v_a_590_, v_s_591_);
lean_dec(v_a_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn(lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___y_617_; lean_object* v___x_638_; 
v___x_638_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_660_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_660_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_660_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_660_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_toQFn_x3f_643_; 
v_toQFn_x3f_643_ = lean_ctor_get(v_a_639_, 4);
if (lean_obj_tag(v_toQFn_x3f_643_) == 1)
{
lean_object* v_val_644_; lean_object* v___x_646_; 
lean_inc_ref(v_toQFn_x3f_643_);
lean_dec(v_a_639_);
v_val_644_ = lean_ctor_get(v_toQFn_x3f_643_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v_toQFn_x3f_643_, 1);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v_val_644_);
v___x_646_ = v___x_641_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_val_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
else
{
lean_object* v_toSemiring_648_; lean_object* v_type_649_; lean_object* v_u_650_; lean_object* v_semiringInst_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
lean_del_object(v___x_641_);
v_toSemiring_648_ = lean_ctor_get(v_a_639_, 0);
lean_inc_ref(v_toSemiring_648_);
lean_dec(v_a_639_);
v_type_649_ = lean_ctor_get(v_toSemiring_648_, 1);
lean_inc_ref(v_type_649_);
v_u_650_ = lean_ctor_get(v_toSemiring_648_, 2);
lean_inc(v_u_650_);
v_semiringInst_651_ = lean_ctor_get(v_toSemiring_648_, 3);
lean_inc_ref(v_semiringInst_651_);
lean_dec_ref(v_toSemiring_648_);
v___x_652_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5));
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_654_, 0, v_u_650_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_mkConst(v___x_652_, v___x_654_);
v___x_656_ = l_Lean_mkAppB(v___x_655_, v_type_649_, v_semiringInst_651_);
v___x_657_ = l_Lean_Meta_Sym_canon(v___x_656_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v___x_659_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_658_, v_a_610_);
v___y_617_ = v___x_659_;
goto v___jp_616_;
}
else
{
v___y_617_ = v___x_657_;
goto v___jp_616_;
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_a_661_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_638_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_638_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
v___jp_616_:
{
if (lean_obj_tag(v___y_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___f_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_a_618_ = lean_ctor_get(v___y_617_, 0);
lean_inc_n(v_a_618_, 2);
lean_dec_ref_known(v___y_617_, 1);
lean_inc(v_a_604_);
v___f_619_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0___boxed), 3, 2);
lean_closure_set(v___f_619_, 0, v_a_604_);
lean_closure_set(v___f_619_, 1, v_a_618_);
v___x_620_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_621_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_620_, v___f_619_, v_a_605_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v___x_621_, 0);
lean_dec(v_unused_629_);
v___x_623_ = v___x_621_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_dec(v___x_621_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_a_618_);
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_618_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v_a_618_);
v_a_630_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_621_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_621_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
return v___y_617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getToQFn___boxed(lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec(v_a_670_);
lean_dec(v_a_669_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(lean_object* v_u_690_, lean_object* v_type_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v_add_701_; lean_object* v___x_702_; 
v___x_697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1));
v___x_698_ = lean_box(0);
v___x_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_699_, 0, v_u_690_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
lean_inc_ref(v___x_699_);
v___x_700_ = l_Lean_mkConst(v___x_697_, v___x_699_);
lean_inc_ref(v_type_691_);
v_add_701_ = l_Lean_Expr_app___override(v___x_700_, v_type_691_);
v___x_702_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_add_701_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_716_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_716_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_716_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_716_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
if (lean_obj_tag(v_a_703_) == 1)
{
lean_object* v_val_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
lean_del_object(v___x_705_);
v_val_707_ = lean_ctor_get(v_a_703_, 0);
lean_inc(v_val_707_);
lean_dec_ref_known(v_a_703_, 1);
v___x_708_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3));
v___x_709_ = l_Lean_mkConst(v___x_708_, v___x_699_);
v___x_710_ = l_Lean_mkAppB(v___x_709_, v_type_691_, v_val_707_);
v___x_711_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_710_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
return v___x_711_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_714_; 
lean_dec(v_a_703_);
lean_dec_ref_known(v___x_699_, 2);
lean_dec_ref(v_type_691_);
v___x_712_ = lean_box(0);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_712_);
v___x_714_ = v___x_705_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_699_, 2);
lean_dec_ref(v_type_691_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___boxed(lean_object* v_u_717_, lean_object* v_type_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_717_, v_type_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(lean_object* v_u_725_, lean_object* v_type_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_725_, v_type_726_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___boxed(lean_object* v_u_739_, lean_object* v_type_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(v_u_739_, v_type_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec(v_a_741_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_s_755_){
_start:
{
lean_object* v_rings_756_; lean_object* v_typeIdOf_757_; lean_object* v_exprToRingId_758_; lean_object* v_semirings_759_; lean_object* v_stypeIdOf_760_; lean_object* v_exprToSemiringId_761_; lean_object* v_ncRings_762_; lean_object* v_exprToNCRingId_763_; lean_object* v_nctypeIdOf_764_; lean_object* v_ncSemirings_765_; lean_object* v_exprToNCSemiringId_766_; lean_object* v_ncstypeIdOf_767_; lean_object* v_steps_768_; uint8_t v_reportedMaxDegreeIssue_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_rings_756_ = lean_ctor_get(v_s_755_, 0);
v_typeIdOf_757_ = lean_ctor_get(v_s_755_, 1);
v_exprToRingId_758_ = lean_ctor_get(v_s_755_, 2);
v_semirings_759_ = lean_ctor_get(v_s_755_, 3);
v_stypeIdOf_760_ = lean_ctor_get(v_s_755_, 4);
v_exprToSemiringId_761_ = lean_ctor_get(v_s_755_, 5);
v_ncRings_762_ = lean_ctor_get(v_s_755_, 6);
v_exprToNCRingId_763_ = lean_ctor_get(v_s_755_, 7);
v_nctypeIdOf_764_ = lean_ctor_get(v_s_755_, 8);
v_ncSemirings_765_ = lean_ctor_get(v_s_755_, 9);
v_exprToNCSemiringId_766_ = lean_ctor_get(v_s_755_, 10);
v_ncstypeIdOf_767_ = lean_ctor_get(v_s_755_, 11);
v_steps_768_ = lean_ctor_get(v_s_755_, 12);
v_reportedMaxDegreeIssue_769_ = lean_ctor_get_uint8(v_s_755_, sizeof(void*)*13);
v___x_770_ = lean_array_get_size(v_semirings_759_);
v___x_771_ = lean_nat_dec_lt(v_a_753_, v___x_770_);
if (v___x_771_ == 0)
{
lean_dec(v_a_754_);
return v_s_755_;
}
else
{
lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_795_; 
lean_inc(v_steps_768_);
lean_inc_ref(v_ncstypeIdOf_767_);
lean_inc_ref(v_exprToNCSemiringId_766_);
lean_inc_ref(v_ncSemirings_765_);
lean_inc_ref(v_nctypeIdOf_764_);
lean_inc_ref(v_exprToNCRingId_763_);
lean_inc_ref(v_ncRings_762_);
lean_inc_ref(v_exprToSemiringId_761_);
lean_inc_ref(v_stypeIdOf_760_);
lean_inc_ref(v_semirings_759_);
lean_inc_ref(v_exprToRingId_758_);
lean_inc_ref(v_typeIdOf_757_);
lean_inc_ref(v_rings_756_);
v_isSharedCheck_795_ = !lean_is_exclusive(v_s_755_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; lean_object* v_unused_797_; lean_object* v_unused_798_; lean_object* v_unused_799_; lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; lean_object* v_unused_803_; lean_object* v_unused_804_; lean_object* v_unused_805_; lean_object* v_unused_806_; lean_object* v_unused_807_; lean_object* v_unused_808_; 
v_unused_796_ = lean_ctor_get(v_s_755_, 12);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_s_755_, 11);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_s_755_, 10);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_s_755_, 9);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_s_755_, 8);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_s_755_, 7);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_s_755_, 6);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_s_755_, 5);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_s_755_, 4);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_s_755_, 3);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_s_755_, 2);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_s_755_, 1);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_s_755_, 0);
lean_dec(v_unused_808_);
v___x_773_ = v_s_755_;
v_isShared_774_ = v_isSharedCheck_795_;
goto v_resetjp_772_;
}
else
{
lean_dec(v_s_755_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_795_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_v_775_; lean_object* v_toSemiring_776_; lean_object* v_ringId_777_; lean_object* v_commSemiringInst_778_; lean_object* v_toQFn_x3f_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_793_; 
v_v_775_ = lean_array_fget(v_semirings_759_, v_a_753_);
v_toSemiring_776_ = lean_ctor_get(v_v_775_, 0);
v_ringId_777_ = lean_ctor_get(v_v_775_, 1);
v_commSemiringInst_778_ = lean_ctor_get(v_v_775_, 2);
v_toQFn_x3f_779_ = lean_ctor_get(v_v_775_, 4);
v_isSharedCheck_793_ = !lean_is_exclusive(v_v_775_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_v_775_, 3);
lean_dec(v_unused_794_);
v___x_781_ = v_v_775_;
v_isShared_782_ = v_isSharedCheck_793_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_toQFn_x3f_779_);
lean_inc(v_commSemiringInst_778_);
lean_inc(v_ringId_777_);
lean_inc(v_toSemiring_776_);
lean_dec(v_v_775_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_793_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v_xs_x27_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_783_ = lean_box(0);
v_xs_x27_784_ = lean_array_fset(v_semirings_759_, v_a_753_, v___x_783_);
v___x_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_785_, 0, v_a_754_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 3, v___x_785_);
v___x_787_ = v___x_781_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_toSemiring_776_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_ringId_777_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_commSemiringInst_778_);
lean_ctor_set(v_reuseFailAlloc_792_, 3, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_792_, 4, v_toQFn_x3f_779_);
v___x_787_ = v_reuseFailAlloc_792_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_array_fset(v_xs_x27_784_, v_a_753_, v___x_787_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 3, v___x_788_);
v___x_790_ = v___x_773_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_rings_756_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_typeIdOf_757_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_exprToRingId_758_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_stypeIdOf_760_);
lean_ctor_set(v_reuseFailAlloc_791_, 5, v_exprToSemiringId_761_);
lean_ctor_set(v_reuseFailAlloc_791_, 6, v_ncRings_762_);
lean_ctor_set(v_reuseFailAlloc_791_, 7, v_exprToNCRingId_763_);
lean_ctor_set(v_reuseFailAlloc_791_, 8, v_nctypeIdOf_764_);
lean_ctor_set(v_reuseFailAlloc_791_, 9, v_ncSemirings_765_);
lean_ctor_set(v_reuseFailAlloc_791_, 10, v_exprToNCSemiringId_766_);
lean_ctor_set(v_reuseFailAlloc_791_, 11, v_ncstypeIdOf_767_);
lean_ctor_set(v_reuseFailAlloc_791_, 12, v_steps_768_);
lean_ctor_set_uint8(v_reuseFailAlloc_791_, sizeof(void*)*13, v_reportedMaxDegreeIssue_769_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed(lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_s_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(v_a_809_, v_a_810_, v_s_811_);
lean_dec(v_a_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_859_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_859_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_859_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_859_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_addRightCancelInst_x3f_830_; 
v_addRightCancelInst_x3f_830_ = lean_ctor_get(v_a_826_, 3);
if (lean_obj_tag(v_addRightCancelInst_x3f_830_) == 1)
{
lean_object* v_val_831_; lean_object* v___x_833_; 
lean_inc_ref(v_addRightCancelInst_x3f_830_);
lean_dec(v_a_826_);
v_val_831_ = lean_ctor_get(v_addRightCancelInst_x3f_830_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v_addRightCancelInst_x3f_830_, 1);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v_val_831_);
v___x_833_ = v___x_828_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_val_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_object* v_toSemiring_835_; lean_object* v_type_836_; lean_object* v_u_837_; lean_object* v___x_838_; 
lean_del_object(v___x_828_);
v_toSemiring_835_ = lean_ctor_get(v_a_826_, 0);
lean_inc_ref(v_toSemiring_835_);
lean_dec(v_a_826_);
v_type_836_ = lean_ctor_get(v_toSemiring_835_, 1);
lean_inc_ref(v_type_836_);
v_u_837_ = lean_ctor_get(v_toSemiring_835_, 2);
lean_inc(v_u_837_);
lean_dec_ref(v_toSemiring_835_);
v___x_838_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_837_, v_type_836_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___f_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc_n(v_a_839_, 2);
lean_dec_ref_known(v___x_838_, 1);
lean_inc(v_a_813_);
v___f_840_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_840_, 0, v_a_813_);
lean_closure_set(v___f_840_, 1, v_a_839_);
v___x_841_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_842_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_841_, v___f_840_, v_a_814_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v___x_842_, 0);
lean_dec(v_unused_850_);
v___x_844_ = v___x_842_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_dec(v___x_842_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v_a_839_);
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_839_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec(v_a_839_);
v_a_851_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_842_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_842_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
v_a_860_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_825_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_825_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___boxed(lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec(v_a_869_);
lean_dec(v_a_868_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_881_, lean_object* v_s_882_){
_start:
{
lean_object* v_id_883_; lean_object* v_type_884_; lean_object* v_u_885_; lean_object* v_semiringInst_886_; lean_object* v_mulFn_x3f_887_; lean_object* v_powFn_x3f_888_; lean_object* v_natCastFn_x3f_889_; lean_object* v_denote_890_; lean_object* v_vars_891_; lean_object* v_varMap_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_900_; 
v_id_883_ = lean_ctor_get(v_s_882_, 0);
v_type_884_ = lean_ctor_get(v_s_882_, 1);
v_u_885_ = lean_ctor_get(v_s_882_, 2);
v_semiringInst_886_ = lean_ctor_get(v_s_882_, 3);
v_mulFn_x3f_887_ = lean_ctor_get(v_s_882_, 5);
v_powFn_x3f_888_ = lean_ctor_get(v_s_882_, 6);
v_natCastFn_x3f_889_ = lean_ctor_get(v_s_882_, 7);
v_denote_890_ = lean_ctor_get(v_s_882_, 8);
v_vars_891_ = lean_ctor_get(v_s_882_, 9);
v_varMap_892_ = lean_ctor_get(v_s_882_, 10);
v_isSharedCheck_900_ = !lean_is_exclusive(v_s_882_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v_s_882_, 4);
lean_dec(v_unused_901_);
v___x_894_ = v_s_882_;
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_varMap_892_);
lean_inc(v_vars_891_);
lean_inc(v_denote_890_);
lean_inc(v_natCastFn_x3f_889_);
lean_inc(v_powFn_x3f_888_);
lean_inc(v_mulFn_x3f_887_);
lean_inc(v_semiringInst_886_);
lean_inc(v_u_885_);
lean_inc(v_type_884_);
lean_inc(v_id_883_);
lean_dec(v_s_882_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v_addFn_881_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 4, v___x_896_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_id_883_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_type_884_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_u_885_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_semiringInst_886_);
lean_ctor_set(v_reuseFailAlloc_899_, 4, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_899_, 5, v_mulFn_x3f_887_);
lean_ctor_set(v_reuseFailAlloc_899_, 6, v_powFn_x3f_888_);
lean_ctor_set(v_reuseFailAlloc_899_, 7, v_natCastFn_x3f_889_);
lean_ctor_set(v_reuseFailAlloc_899_, 8, v_denote_890_);
lean_ctor_set(v_reuseFailAlloc_899_, 9, v_vars_891_);
lean_ctor_set(v_reuseFailAlloc_899_, 10, v_varMap_892_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_902_, lean_object* v_addFn_903_, lean_object* v_____r_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = lean_apply_2(v_toPure_902_, lean_box(0), v_addFn_903_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_906_, lean_object* v_modifySemiring_907_, lean_object* v_toBind_908_, lean_object* v_addFn_909_){
_start:
{
lean_object* v___f_910_; lean_object* v___f_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_inc_ref(v_addFn_909_);
v___f_910_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_910_, 0, v_addFn_909_);
v___f_911_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_911_, 0, v_toPure_906_);
lean_closure_set(v___f_911_, 1, v_addFn_909_);
v___x_912_ = lean_apply_1(v_modifySemiring_907_, v___f_910_);
v___x_913_ = lean_apply_4(v_toBind_908_, lean_box(0), lean_box(0), v___x_912_, v___f_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3(lean_object* v_toPure_931_, lean_object* v_inst_932_, lean_object* v_inst_933_, lean_object* v_inst_934_, lean_object* v_inst_935_, lean_object* v_toBind_936_, lean_object* v___f_937_, lean_object* v_s_938_){
_start:
{
lean_object* v_addFn_x3f_939_; 
v_addFn_x3f_939_ = lean_ctor_get(v_s_938_, 4);
if (lean_obj_tag(v_addFn_x3f_939_) == 1)
{
lean_object* v_val_940_; lean_object* v___x_941_; 
lean_inc_ref(v_addFn_x3f_939_);
lean_dec_ref(v_s_938_);
lean_dec(v___f_937_);
lean_dec(v_toBind_936_);
lean_dec_ref(v_inst_935_);
lean_dec_ref(v_inst_934_);
lean_dec_ref(v_inst_933_);
lean_dec(v_inst_932_);
v_val_940_ = lean_ctor_get(v_addFn_x3f_939_, 0);
lean_inc(v_val_940_);
lean_dec_ref_known(v_addFn_x3f_939_, 1);
v___x_941_ = lean_apply_2(v_toPure_931_, lean_box(0), v_val_940_);
return v___x_941_;
}
else
{
lean_object* v_type_942_; lean_object* v_u_943_; lean_object* v_semiringInst_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_expectedInst_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec(v_toPure_931_);
v_type_942_ = lean_ctor_get(v_s_938_, 1);
lean_inc_ref_n(v_type_942_, 3);
v_u_943_ = lean_ctor_get(v_s_938_, 2);
lean_inc_n(v_u_943_, 2);
v_semiringInst_944_ = lean_ctor_get(v_s_938_, 3);
lean_inc_ref(v_semiringInst_944_);
lean_dec_ref(v_s_938_);
v___x_945_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_946_ = lean_box(0);
v___x_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_947_, 0, v_u_943_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
lean_inc_ref(v___x_947_);
v___x_948_ = l_Lean_mkConst(v___x_945_, v___x_947_);
v___x_949_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_950_ = l_Lean_mkConst(v___x_949_, v___x_947_);
v___x_951_ = l_Lean_mkAppB(v___x_950_, v_type_942_, v_semiringInst_944_);
v_expectedInst_952_ = l_Lean_mkAppB(v___x_948_, v_type_942_, v___x_951_);
v___x_953_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6));
v___x_954_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8));
v___x_955_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_932_, v_inst_933_, v_inst_934_, v_inst_935_, v_type_942_, v_u_943_, v___x_953_, v___x_954_, v_expectedInst_952_);
v___x_956_ = lean_apply_4(v_toBind_936_, lean_box(0), lean_box(0), v___x_955_, v___f_937_);
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(lean_object* v_inst_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_inst_961_){
_start:
{
lean_object* v_toApplicative_962_; lean_object* v_toBind_963_; lean_object* v_getSemiring_964_; lean_object* v_modifySemiring_965_; lean_object* v_toPure_966_; lean_object* v___f_967_; lean_object* v___f_968_; lean_object* v___x_969_; 
v_toApplicative_962_ = lean_ctor_get(v_inst_959_, 0);
v_toBind_963_ = lean_ctor_get(v_inst_959_, 1);
lean_inc_n(v_toBind_963_, 3);
v_getSemiring_964_ = lean_ctor_get(v_inst_961_, 0);
lean_inc(v_getSemiring_964_);
v_modifySemiring_965_ = lean_ctor_get(v_inst_961_, 1);
lean_inc(v_modifySemiring_965_);
lean_dec_ref(v_inst_961_);
v_toPure_966_ = lean_ctor_get(v_toApplicative_962_, 1);
lean_inc_n(v_toPure_966_, 2);
v___f_967_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_967_, 0, v_toPure_966_);
lean_closure_set(v___f_967_, 1, v_modifySemiring_965_);
lean_closure_set(v___f_967_, 2, v_toBind_963_);
v___f_968_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_968_, 0, v_toPure_966_);
lean_closure_set(v___f_968_, 1, v_inst_957_);
lean_closure_set(v___f_968_, 2, v_inst_958_);
lean_closure_set(v___f_968_, 3, v_inst_959_);
lean_closure_set(v___f_968_, 4, v_inst_960_);
lean_closure_set(v___f_968_, 5, v_toBind_963_);
lean_closure_set(v___f_968_, 6, v___f_967_);
v___x_969_ = lean_apply_4(v_toBind_963_, lean_box(0), lean_box(0), v_getSemiring_964_, v___f_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27(lean_object* v_m_970_, lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_inst_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(v_inst_971_, v_inst_972_, v_inst_973_, v_inst_974_, v_inst_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_977_, lean_object* v_s_978_){
_start:
{
lean_object* v_id_979_; lean_object* v_type_980_; lean_object* v_u_981_; lean_object* v_semiringInst_982_; lean_object* v_addFn_x3f_983_; lean_object* v_powFn_x3f_984_; lean_object* v_natCastFn_x3f_985_; lean_object* v_denote_986_; lean_object* v_vars_987_; lean_object* v_varMap_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_996_; 
v_id_979_ = lean_ctor_get(v_s_978_, 0);
v_type_980_ = lean_ctor_get(v_s_978_, 1);
v_u_981_ = lean_ctor_get(v_s_978_, 2);
v_semiringInst_982_ = lean_ctor_get(v_s_978_, 3);
v_addFn_x3f_983_ = lean_ctor_get(v_s_978_, 4);
v_powFn_x3f_984_ = lean_ctor_get(v_s_978_, 6);
v_natCastFn_x3f_985_ = lean_ctor_get(v_s_978_, 7);
v_denote_986_ = lean_ctor_get(v_s_978_, 8);
v_vars_987_ = lean_ctor_get(v_s_978_, 9);
v_varMap_988_ = lean_ctor_get(v_s_978_, 10);
v_isSharedCheck_996_ = !lean_is_exclusive(v_s_978_);
if (v_isSharedCheck_996_ == 0)
{
lean_object* v_unused_997_; 
v_unused_997_ = lean_ctor_get(v_s_978_, 5);
lean_dec(v_unused_997_);
v___x_990_ = v_s_978_;
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_varMap_988_);
lean_inc(v_vars_987_);
lean_inc(v_denote_986_);
lean_inc(v_natCastFn_x3f_985_);
lean_inc(v_powFn_x3f_984_);
lean_inc(v_addFn_x3f_983_);
lean_inc(v_semiringInst_982_);
lean_inc(v_u_981_);
lean_inc(v_type_980_);
lean_inc(v_id_979_);
lean_dec(v_s_978_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v_mulFn_977_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 5, v___x_992_);
v___x_994_ = v___x_990_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_id_979_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_type_980_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_u_981_);
lean_ctor_set(v_reuseFailAlloc_995_, 3, v_semiringInst_982_);
lean_ctor_set(v_reuseFailAlloc_995_, 4, v_addFn_x3f_983_);
lean_ctor_set(v_reuseFailAlloc_995_, 5, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_995_, 6, v_powFn_x3f_984_);
lean_ctor_set(v_reuseFailAlloc_995_, 7, v_natCastFn_x3f_985_);
lean_ctor_set(v_reuseFailAlloc_995_, 8, v_denote_986_);
lean_ctor_set(v_reuseFailAlloc_995_, 9, v_vars_987_);
lean_ctor_set(v_reuseFailAlloc_995_, 10, v_varMap_988_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_998_, lean_object* v_mulFn_999_, lean_object* v_____r_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_apply_2(v_toPure_998_, lean_box(0), v_mulFn_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_1002_, lean_object* v_modifySemiring_1003_, lean_object* v_toBind_1004_, lean_object* v_mulFn_1005_){
_start:
{
lean_object* v___f_1006_; lean_object* v___f_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_inc_ref(v_mulFn_1005_);
v___f_1006_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1006_, 0, v_mulFn_1005_);
v___f_1007_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1007_, 0, v_toPure_1002_);
lean_closure_set(v___f_1007_, 1, v_mulFn_1005_);
v___x_1008_ = lean_apply_1(v_modifySemiring_1003_, v___f_1006_);
v___x_1009_ = lean_apply_4(v_toBind_1004_, lean_box(0), lean_box(0), v___x_1008_, v___f_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3(lean_object* v_toPure_1026_, lean_object* v_inst_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_toBind_1031_, lean_object* v___f_1032_, lean_object* v_s_1033_){
_start:
{
lean_object* v_mulFn_x3f_1034_; 
v_mulFn_x3f_1034_ = lean_ctor_get(v_s_1033_, 5);
if (lean_obj_tag(v_mulFn_x3f_1034_) == 1)
{
lean_object* v_val_1035_; lean_object* v___x_1036_; 
lean_inc_ref(v_mulFn_x3f_1034_);
lean_dec_ref(v_s_1033_);
lean_dec(v___f_1032_);
lean_dec(v_toBind_1031_);
lean_dec_ref(v_inst_1030_);
lean_dec_ref(v_inst_1029_);
lean_dec_ref(v_inst_1028_);
lean_dec(v_inst_1027_);
v_val_1035_ = lean_ctor_get(v_mulFn_x3f_1034_, 0);
lean_inc(v_val_1035_);
lean_dec_ref_known(v_mulFn_x3f_1034_, 1);
v___x_1036_ = lean_apply_2(v_toPure_1026_, lean_box(0), v_val_1035_);
return v___x_1036_;
}
else
{
lean_object* v_type_1037_; lean_object* v_u_1038_; lean_object* v_semiringInst_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_expectedInst_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec(v_toPure_1026_);
v_type_1037_ = lean_ctor_get(v_s_1033_, 1);
lean_inc_ref_n(v_type_1037_, 3);
v_u_1038_ = lean_ctor_get(v_s_1033_, 2);
lean_inc_n(v_u_1038_, 2);
v_semiringInst_1039_ = lean_ctor_get(v_s_1033_, 3);
lean_inc_ref(v_semiringInst_1039_);
lean_dec_ref(v_s_1033_);
v___x_1040_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_1041_ = lean_box(0);
v___x_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_u_1038_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
lean_inc_ref(v___x_1042_);
v___x_1043_ = l_Lean_mkConst(v___x_1040_, v___x_1042_);
v___x_1044_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_1045_ = l_Lean_mkConst(v___x_1044_, v___x_1042_);
v___x_1046_ = l_Lean_mkAppB(v___x_1045_, v_type_1037_, v_semiringInst_1039_);
v_expectedInst_1047_ = l_Lean_mkAppB(v___x_1043_, v_type_1037_, v___x_1046_);
v___x_1048_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5));
v___x_1049_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7));
v___x_1050_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(v_inst_1027_, v_inst_1028_, v_inst_1029_, v_inst_1030_, v_type_1037_, v_u_1038_, v___x_1048_, v___x_1049_, v_expectedInst_1047_);
v___x_1051_ = lean_apply_4(v_toBind_1031_, lean_box(0), lean_box(0), v___x_1050_, v___f_1032_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_){
_start:
{
lean_object* v_toApplicative_1057_; lean_object* v_toBind_1058_; lean_object* v_getSemiring_1059_; lean_object* v_modifySemiring_1060_; lean_object* v_toPure_1061_; lean_object* v___f_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; 
v_toApplicative_1057_ = lean_ctor_get(v_inst_1054_, 0);
v_toBind_1058_ = lean_ctor_get(v_inst_1054_, 1);
lean_inc_n(v_toBind_1058_, 3);
v_getSemiring_1059_ = lean_ctor_get(v_inst_1056_, 0);
lean_inc(v_getSemiring_1059_);
v_modifySemiring_1060_ = lean_ctor_get(v_inst_1056_, 1);
lean_inc(v_modifySemiring_1060_);
lean_dec_ref(v_inst_1056_);
v_toPure_1061_ = lean_ctor_get(v_toApplicative_1057_, 1);
lean_inc_n(v_toPure_1061_, 2);
v___f_1062_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1062_, 0, v_toPure_1061_);
lean_closure_set(v___f_1062_, 1, v_modifySemiring_1060_);
lean_closure_set(v___f_1062_, 2, v_toBind_1058_);
v___f_1063_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1063_, 0, v_toPure_1061_);
lean_closure_set(v___f_1063_, 1, v_inst_1052_);
lean_closure_set(v___f_1063_, 2, v_inst_1053_);
lean_closure_set(v___f_1063_, 3, v_inst_1054_);
lean_closure_set(v___f_1063_, 4, v_inst_1055_);
lean_closure_set(v___f_1063_, 5, v_toBind_1058_);
lean_closure_set(v___f_1063_, 6, v___f_1062_);
v___x_1064_ = lean_apply_4(v_toBind_1058_, lean_box(0), lean_box(0), v_getSemiring_1059_, v___f_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27(lean_object* v_m_1065_, lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(v_inst_1066_, v_inst_1067_, v_inst_1068_, v_inst_1069_, v_inst_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_1072_, lean_object* v_s_1073_){
_start:
{
lean_object* v_id_1074_; lean_object* v_type_1075_; lean_object* v_u_1076_; lean_object* v_semiringInst_1077_; lean_object* v_addFn_x3f_1078_; lean_object* v_mulFn_x3f_1079_; lean_object* v_natCastFn_x3f_1080_; lean_object* v_denote_1081_; lean_object* v_vars_1082_; lean_object* v_varMap_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1091_; 
v_id_1074_ = lean_ctor_get(v_s_1073_, 0);
v_type_1075_ = lean_ctor_get(v_s_1073_, 1);
v_u_1076_ = lean_ctor_get(v_s_1073_, 2);
v_semiringInst_1077_ = lean_ctor_get(v_s_1073_, 3);
v_addFn_x3f_1078_ = lean_ctor_get(v_s_1073_, 4);
v_mulFn_x3f_1079_ = lean_ctor_get(v_s_1073_, 5);
v_natCastFn_x3f_1080_ = lean_ctor_get(v_s_1073_, 7);
v_denote_1081_ = lean_ctor_get(v_s_1073_, 8);
v_vars_1082_ = lean_ctor_get(v_s_1073_, 9);
v_varMap_1083_ = lean_ctor_get(v_s_1073_, 10);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_s_1073_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v_s_1073_, 6);
lean_dec(v_unused_1092_);
v___x_1085_ = v_s_1073_;
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_varMap_1083_);
lean_inc(v_vars_1082_);
lean_inc(v_denote_1081_);
lean_inc(v_natCastFn_x3f_1080_);
lean_inc(v_mulFn_x3f_1079_);
lean_inc(v_addFn_x3f_1078_);
lean_inc(v_semiringInst_1077_);
lean_inc(v_u_1076_);
lean_inc(v_type_1075_);
lean_inc(v_id_1074_);
lean_dec(v_s_1073_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_powFn_1072_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 6, v___x_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_id_1074_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_type_1075_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_u_1076_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_semiringInst_1077_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_addFn_x3f_1078_);
lean_ctor_set(v_reuseFailAlloc_1090_, 5, v_mulFn_x3f_1079_);
lean_ctor_set(v_reuseFailAlloc_1090_, 6, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1090_, 7, v_natCastFn_x3f_1080_);
lean_ctor_set(v_reuseFailAlloc_1090_, 8, v_denote_1081_);
lean_ctor_set(v_reuseFailAlloc_1090_, 9, v_vars_1082_);
lean_ctor_set(v_reuseFailAlloc_1090_, 10, v_varMap_1083_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_1093_, lean_object* v_powFn_1094_, lean_object* v_____r_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_apply_2(v_toPure_1093_, lean_box(0), v_powFn_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_1097_, lean_object* v_modifySemiring_1098_, lean_object* v_toBind_1099_, lean_object* v_powFn_1100_){
_start:
{
lean_object* v___f_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_inc_ref(v_powFn_1100_);
v___f_1101_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1101_, 0, v_powFn_1100_);
v___f_1102_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1102_, 0, v_toPure_1097_);
lean_closure_set(v___f_1102_, 1, v_powFn_1100_);
v___x_1103_ = lean_apply_1(v_modifySemiring_1098_, v___f_1101_);
v___x_1104_ = lean_apply_4(v_toBind_1099_, lean_box(0), lean_box(0), v___x_1103_, v___f_1102_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3(lean_object* v_toPure_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_toBind_1110_, lean_object* v___f_1111_, lean_object* v_s_1112_){
_start:
{
lean_object* v_powFn_x3f_1113_; 
v_powFn_x3f_1113_ = lean_ctor_get(v_s_1112_, 6);
if (lean_obj_tag(v_powFn_x3f_1113_) == 1)
{
lean_object* v_val_1114_; lean_object* v___x_1115_; 
lean_inc_ref(v_powFn_x3f_1113_);
lean_dec_ref(v_s_1112_);
lean_dec(v___f_1111_);
lean_dec(v_toBind_1110_);
lean_dec_ref(v_inst_1109_);
lean_dec_ref(v_inst_1108_);
lean_dec_ref(v_inst_1107_);
lean_dec(v_inst_1106_);
v_val_1114_ = lean_ctor_get(v_powFn_x3f_1113_, 0);
lean_inc(v_val_1114_);
lean_dec_ref_known(v_powFn_x3f_1113_, 1);
v___x_1115_ = lean_apply_2(v_toPure_1105_, lean_box(0), v_val_1114_);
return v___x_1115_;
}
else
{
lean_object* v_type_1116_; lean_object* v_u_1117_; lean_object* v_semiringInst_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec(v_toPure_1105_);
v_type_1116_ = lean_ctor_get(v_s_1112_, 1);
lean_inc_ref(v_type_1116_);
v_u_1117_ = lean_ctor_get(v_s_1112_, 2);
lean_inc(v_u_1117_);
v_semiringInst_1118_ = lean_ctor_get(v_s_1112_, 3);
lean_inc_ref(v_semiringInst_1118_);
lean_dec_ref(v_s_1112_);
v___x_1119_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(v_inst_1106_, v_inst_1107_, v_inst_1108_, v_inst_1109_, v_u_1117_, v_type_1116_, v_semiringInst_1118_);
v___x_1120_ = lean_apply_4(v_toBind_1110_, lean_box(0), lean_box(0), v___x_1119_, v___f_1111_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_){
_start:
{
lean_object* v_toApplicative_1126_; lean_object* v_toBind_1127_; lean_object* v_getSemiring_1128_; lean_object* v_modifySemiring_1129_; lean_object* v_toPure_1130_; lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; 
v_toApplicative_1126_ = lean_ctor_get(v_inst_1123_, 0);
v_toBind_1127_ = lean_ctor_get(v_inst_1123_, 1);
lean_inc_n(v_toBind_1127_, 3);
v_getSemiring_1128_ = lean_ctor_get(v_inst_1125_, 0);
lean_inc(v_getSemiring_1128_);
v_modifySemiring_1129_ = lean_ctor_get(v_inst_1125_, 1);
lean_inc(v_modifySemiring_1129_);
lean_dec_ref(v_inst_1125_);
v_toPure_1130_ = lean_ctor_get(v_toApplicative_1126_, 1);
lean_inc_n(v_toPure_1130_, 2);
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1131_, 0, v_toPure_1130_);
lean_closure_set(v___f_1131_, 1, v_modifySemiring_1129_);
lean_closure_set(v___f_1131_, 2, v_toBind_1127_);
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1132_, 0, v_toPure_1130_);
lean_closure_set(v___f_1132_, 1, v_inst_1121_);
lean_closure_set(v___f_1132_, 2, v_inst_1122_);
lean_closure_set(v___f_1132_, 3, v_inst_1123_);
lean_closure_set(v___f_1132_, 4, v_inst_1124_);
lean_closure_set(v___f_1132_, 5, v_toBind_1127_);
lean_closure_set(v___f_1132_, 6, v___f_1131_);
v___x_1133_ = lean_apply_4(v_toBind_1127_, lean_box(0), lean_box(0), v_getSemiring_1128_, v___f_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27(lean_object* v_m_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(v_inst_1135_, v_inst_1136_, v_inst_1137_, v_inst_1138_, v_inst_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_1141_, lean_object* v_s_1142_){
_start:
{
lean_object* v_id_1143_; lean_object* v_type_1144_; lean_object* v_u_1145_; lean_object* v_semiringInst_1146_; lean_object* v_addFn_x3f_1147_; lean_object* v_mulFn_x3f_1148_; lean_object* v_powFn_x3f_1149_; lean_object* v_denote_1150_; lean_object* v_vars_1151_; lean_object* v_varMap_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1160_; 
v_id_1143_ = lean_ctor_get(v_s_1142_, 0);
v_type_1144_ = lean_ctor_get(v_s_1142_, 1);
v_u_1145_ = lean_ctor_get(v_s_1142_, 2);
v_semiringInst_1146_ = lean_ctor_get(v_s_1142_, 3);
v_addFn_x3f_1147_ = lean_ctor_get(v_s_1142_, 4);
v_mulFn_x3f_1148_ = lean_ctor_get(v_s_1142_, 5);
v_powFn_x3f_1149_ = lean_ctor_get(v_s_1142_, 6);
v_denote_1150_ = lean_ctor_get(v_s_1142_, 8);
v_vars_1151_ = lean_ctor_get(v_s_1142_, 9);
v_varMap_1152_ = lean_ctor_get(v_s_1142_, 10);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_s_1142_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v_s_1142_, 7);
lean_dec(v_unused_1161_);
v___x_1154_ = v_s_1142_;
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_varMap_1152_);
lean_inc(v_vars_1151_);
lean_inc(v_denote_1150_);
lean_inc(v_powFn_x3f_1149_);
lean_inc(v_mulFn_x3f_1148_);
lean_inc(v_addFn_x3f_1147_);
lean_inc(v_semiringInst_1146_);
lean_inc(v_u_1145_);
lean_inc(v_type_1144_);
lean_inc(v_id_1143_);
lean_dec(v_s_1142_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_natCastFn_1141_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 7, v___x_1156_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_id_1143_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_type_1144_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_u_1145_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_semiringInst_1146_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_addFn_x3f_1147_);
lean_ctor_set(v_reuseFailAlloc_1159_, 5, v_mulFn_x3f_1148_);
lean_ctor_set(v_reuseFailAlloc_1159_, 6, v_powFn_x3f_1149_);
lean_ctor_set(v_reuseFailAlloc_1159_, 7, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1159_, 8, v_denote_1150_);
lean_ctor_set(v_reuseFailAlloc_1159_, 9, v_vars_1151_);
lean_ctor_set(v_reuseFailAlloc_1159_, 10, v_varMap_1152_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_1162_, lean_object* v_natCastFn_1163_, lean_object* v_____r_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_apply_2(v_toPure_1162_, lean_box(0), v_natCastFn_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_1166_, lean_object* v_modifySemiring_1167_, lean_object* v_toBind_1168_, lean_object* v_natCastFn_1169_){
_start:
{
lean_object* v___f_1170_; lean_object* v___f_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_inc_ref(v_natCastFn_1169_);
v___f_1170_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1170_, 0, v_natCastFn_1169_);
v___f_1171_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1171_, 0, v_toPure_1166_);
lean_closure_set(v___f_1171_, 1, v_natCastFn_1169_);
v___x_1172_ = lean_apply_1(v_modifySemiring_1167_, v___f_1170_);
v___x_1173_ = lean_apply_4(v_toBind_1168_, lean_box(0), lean_box(0), v___x_1172_, v___f_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3(lean_object* v_toPure_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_toBind_1178_, lean_object* v___f_1179_, lean_object* v_s_1180_){
_start:
{
lean_object* v_natCastFn_x3f_1181_; 
v_natCastFn_x3f_1181_ = lean_ctor_get(v_s_1180_, 7);
if (lean_obj_tag(v_natCastFn_x3f_1181_) == 1)
{
lean_object* v_val_1182_; lean_object* v___x_1183_; 
lean_inc_ref(v_natCastFn_x3f_1181_);
lean_dec_ref(v_s_1180_);
lean_dec(v___f_1179_);
lean_dec(v_toBind_1178_);
lean_dec_ref(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
lean_dec(v_inst_1175_);
v_val_1182_ = lean_ctor_get(v_natCastFn_x3f_1181_, 0);
lean_inc(v_val_1182_);
lean_dec_ref_known(v_natCastFn_x3f_1181_, 1);
v___x_1183_ = lean_apply_2(v_toPure_1174_, lean_box(0), v_val_1182_);
return v___x_1183_;
}
else
{
lean_object* v_type_1184_; lean_object* v_u_1185_; lean_object* v_semiringInst_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec(v_toPure_1174_);
v_type_1184_ = lean_ctor_get(v_s_1180_, 1);
lean_inc_ref(v_type_1184_);
v_u_1185_ = lean_ctor_get(v_s_1180_, 2);
lean_inc(v_u_1185_);
v_semiringInst_1186_ = lean_ctor_get(v_s_1180_, 3);
lean_inc_ref(v_semiringInst_1186_);
lean_dec_ref(v_s_1180_);
v___x_1187_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(v_inst_1175_, v_inst_1176_, v_inst_1177_, v_u_1185_, v_type_1184_, v_semiringInst_1186_);
v___x_1188_ = lean_apply_4(v_toBind_1178_, lean_box(0), lean_box(0), v___x_1187_, v___f_1179_);
return v___x_1188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_){
_start:
{
lean_object* v_toApplicative_1193_; lean_object* v_toBind_1194_; lean_object* v_getSemiring_1195_; lean_object* v_modifySemiring_1196_; lean_object* v_toPure_1197_; lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v___x_1200_; 
v_toApplicative_1193_ = lean_ctor_get(v_inst_1190_, 0);
v_toBind_1194_ = lean_ctor_get(v_inst_1190_, 1);
lean_inc_n(v_toBind_1194_, 3);
v_getSemiring_1195_ = lean_ctor_get(v_inst_1192_, 0);
lean_inc(v_getSemiring_1195_);
v_modifySemiring_1196_ = lean_ctor_get(v_inst_1192_, 1);
lean_inc(v_modifySemiring_1196_);
lean_dec_ref(v_inst_1192_);
v_toPure_1197_ = lean_ctor_get(v_toApplicative_1193_, 1);
lean_inc_n(v_toPure_1197_, 2);
v___f_1198_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1198_, 0, v_toPure_1197_);
lean_closure_set(v___f_1198_, 1, v_modifySemiring_1196_);
lean_closure_set(v___f_1198_, 2, v_toBind_1194_);
v___f_1199_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1199_, 0, v_toPure_1197_);
lean_closure_set(v___f_1199_, 1, v_inst_1189_);
lean_closure_set(v___f_1199_, 2, v_inst_1190_);
lean_closure_set(v___f_1199_, 3, v_inst_1191_);
lean_closure_set(v___f_1199_, 4, v_toBind_1194_);
lean_closure_set(v___f_1199_, 5, v___f_1198_);
v___x_1200_ = lean_apply_4(v_toBind_1194_, lean_box(0), lean_box(0), v_getSemiring_1195_, v___f_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27(lean_object* v_m_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(v_inst_1202_, v_inst_1203_, v_inst_1204_, v_inst_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1207_, lean_object* v_vals_1208_, lean_object* v_i_1209_, lean_object* v_k_1210_){
_start:
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = lean_array_get_size(v_keys_1207_);
v___x_1212_ = lean_nat_dec_lt(v_i_1209_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec(v_i_1209_);
v___x_1213_ = lean_box(0);
return v___x_1213_;
}
else
{
lean_object* v_k_x27_1214_; uint8_t v___x_1215_; 
v_k_x27_1214_ = lean_array_fget_borrowed(v_keys_1207_, v_i_1209_);
v___x_1215_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_1210_, v_k_x27_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_unsigned_to_nat(1u);
v___x_1217_ = lean_nat_add(v_i_1209_, v___x_1216_);
lean_dec(v_i_1209_);
v_i_1209_ = v___x_1217_;
goto _start;
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_array_fget_borrowed(v_vals_1208_, v_i_1209_);
lean_dec(v_i_1209_);
lean_inc(v___x_1219_);
v___x_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1221_, lean_object* v_vals_1222_, lean_object* v_i_1223_, lean_object* v_k_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1221_, v_vals_1222_, v_i_1223_, v_k_1224_);
lean_dec_ref(v_k_1224_);
lean_dec_ref(v_vals_1222_);
lean_dec_ref(v_keys_1221_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(lean_object* v_x_1226_, size_t v_x_1227_, lean_object* v_x_1228_){
_start:
{
if (lean_obj_tag(v_x_1226_) == 0)
{
lean_object* v_es_1229_; lean_object* v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; lean_object* v_j_1233_; lean_object* v___x_1234_; 
v_es_1229_ = lean_ctor_get(v_x_1226_, 0);
v___x_1230_ = lean_box(2);
v___x_1231_ = ((size_t)31ULL);
v___x_1232_ = lean_usize_land(v_x_1227_, v___x_1231_);
v_j_1233_ = lean_usize_to_nat(v___x_1232_);
v___x_1234_ = lean_array_get_borrowed(v___x_1230_, v_es_1229_, v_j_1233_);
lean_dec(v_j_1233_);
switch(lean_obj_tag(v___x_1234_))
{
case 0:
{
lean_object* v_key_1235_; lean_object* v_val_1236_; uint8_t v___x_1237_; 
v_key_1235_ = lean_ctor_get(v___x_1234_, 0);
v_val_1236_ = lean_ctor_get(v___x_1234_, 1);
v___x_1237_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1228_, v_key_1235_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_box(0);
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; 
lean_inc(v_val_1236_);
v___x_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1239_, 0, v_val_1236_);
return v___x_1239_;
}
}
case 1:
{
lean_object* v_node_1240_; size_t v___x_1241_; size_t v___x_1242_; 
v_node_1240_ = lean_ctor_get(v___x_1234_, 0);
v___x_1241_ = ((size_t)5ULL);
v___x_1242_ = lean_usize_shift_right(v_x_1227_, v___x_1241_);
v_x_1226_ = v_node_1240_;
v_x_1227_ = v___x_1242_;
goto _start;
}
default: 
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_box(0);
return v___x_1244_;
}
}
}
else
{
lean_object* v_ks_1245_; lean_object* v_vs_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_ks_1245_ = lean_ctor_get(v_x_1226_, 0);
v_vs_1246_ = lean_ctor_get(v_x_1226_, 1);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1245_, v_vs_1246_, v___x_1247_, v_x_1228_);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1249_, lean_object* v_x_1250_, lean_object* v_x_1251_){
_start:
{
size_t v_x_851__boxed_1252_; lean_object* v_res_1253_; 
v_x_851__boxed_1252_ = lean_unbox_usize(v_x_1250_);
lean_dec(v_x_1250_);
v_res_1253_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1249_, v_x_851__boxed_1252_, v_x_1251_);
lean_dec_ref(v_x_1251_);
lean_dec_ref(v_x_1249_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(lean_object* v_x_1254_, lean_object* v_x_1255_){
_start:
{
uint64_t v___x_1256_; size_t v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1255_);
v___x_1257_ = lean_uint64_to_usize(v___x_1256_);
v___x_1258_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1254_, v___x_1257_, v_x_1255_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_1259_, v_x_1260_);
lean_dec_ref(v_x_1260_);
lean_dec_ref(v_x_1259_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(lean_object* v_e_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1276_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1276_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1276_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v_exprToSemiringId_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
v_exprToSemiringId_1271_ = lean_ctor_get(v_a_1267_, 5);
lean_inc_ref(v_exprToSemiringId_1271_);
lean_dec(v_a_1267_);
v___x_1272_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_exprToSemiringId_1271_, v_e_1262_);
lean_dec_ref(v_exprToSemiringId_1271_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1272_);
v___x_1274_ = v___x_1269_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
v_a_1277_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1266_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1266_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg___boxed(lean_object* v_e_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1285_, v_a_1286_, v_a_1287_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_e_1285_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(lean_object* v_e_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1290_, v_a_1291_, v_a_1299_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(lean_object* v_e_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(v_e_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_e_1303_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(lean_object* v_00_u03b2_1316_, lean_object* v_x_1317_, lean_object* v_x_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_1317_, v_x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(lean_object* v_00_u03b2_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(v_00_u03b2_1320_, v_x_1321_, v_x_1322_);
lean_dec_ref(v_x_1322_);
lean_dec_ref(v_x_1321_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1324_, lean_object* v_x_1325_, size_t v_x_1326_, lean_object* v_x_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_1325_, v_x_1326_, v_x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_){
_start:
{
size_t v_x_962__boxed_1333_; lean_object* v_res_1334_; 
v_x_962__boxed_1333_ = lean_unbox_usize(v_x_1331_);
lean_dec(v_x_1331_);
v_res_1334_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(v_00_u03b2_1329_, v_x_1330_, v_x_962__boxed_1333_, v_x_1332_);
lean_dec_ref(v_x_1332_);
lean_dec_ref(v_x_1330_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1335_, lean_object* v_keys_1336_, lean_object* v_vals_1337_, lean_object* v_heq_1338_, lean_object* v_i_1339_, lean_object* v_k_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1336_, v_vals_1337_, v_i_1339_, v_k_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1342_, lean_object* v_keys_1343_, lean_object* v_vals_1344_, lean_object* v_heq_1345_, lean_object* v_i_1346_, lean_object* v_k_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1342_, v_keys_1343_, v_vals_1344_, v_heq_1345_, v_i_1346_, v_k_1347_);
lean_dec_ref(v_k_1347_);
lean_dec_ref(v_vals_1344_);
lean_dec_ref(v_keys_1343_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
lean_object* v_ks_1353_; lean_object* v_vs_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1378_; 
v_ks_1353_ = lean_ctor_get(v_x_1349_, 0);
v_vs_1354_ = lean_ctor_get(v_x_1349_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_x_1349_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1356_ = v_x_1349_;
v_isShared_1357_ = v_isSharedCheck_1378_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_vs_1354_);
lean_inc(v_ks_1353_);
lean_dec(v_x_1349_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1378_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = lean_array_get_size(v_ks_1353_);
v___x_1359_ = lean_nat_dec_lt(v_x_1350_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_dec(v_x_1350_);
v___x_1360_ = lean_array_push(v_ks_1353_, v_x_1351_);
v___x_1361_ = lean_array_push(v_vs_1354_, v_x_1352_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v___x_1361_);
lean_ctor_set(v___x_1356_, 0, v___x_1360_);
v___x_1363_ = v___x_1356_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
else
{
lean_object* v_k_x27_1365_; uint8_t v___x_1366_; 
v_k_x27_1365_ = lean_array_fget_borrowed(v_ks_1353_, v_x_1350_);
v___x_1366_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1351_, v_k_x27_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1368_; 
if (v_isShared_1357_ == 0)
{
v___x_1368_ = v___x_1356_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_ks_1353_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_vs_1354_);
v___x_1368_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_nat_add(v_x_1350_, v___x_1369_);
lean_dec(v_x_1350_);
v_x_1349_ = v___x_1368_;
v_x_1350_ = v___x_1370_;
goto _start;
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1373_ = lean_array_fset(v_ks_1353_, v_x_1350_, v_x_1351_);
v___x_1374_ = lean_array_fset(v_vs_1354_, v_x_1350_, v_x_1352_);
lean_dec(v_x_1350_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v___x_1374_);
lean_ctor_set(v___x_1356_, 0, v___x_1373_);
v___x_1376_ = v___x_1356_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1379_, lean_object* v_k_1380_, lean_object* v_v_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1379_, v___x_1382_, v_k_1380_, v_v_1381_);
return v___x_1383_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(lean_object* v_x_1385_, size_t v_x_1386_, size_t v_x_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_){
_start:
{
if (lean_obj_tag(v_x_1385_) == 0)
{
lean_object* v_es_1390_; size_t v___x_1391_; size_t v___x_1392_; lean_object* v_j_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_es_1390_ = lean_ctor_get(v_x_1385_, 0);
v___x_1391_ = ((size_t)31ULL);
v___x_1392_ = lean_usize_land(v_x_1386_, v___x_1391_);
v_j_1393_ = lean_usize_to_nat(v___x_1392_);
v___x_1394_ = lean_array_get_size(v_es_1390_);
v___x_1395_ = lean_nat_dec_lt(v_j_1393_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_dec(v_j_1393_);
lean_dec(v_x_1389_);
lean_dec_ref(v_x_1388_);
return v_x_1385_;
}
else
{
lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1434_; 
lean_inc_ref(v_es_1390_);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_x_1385_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; 
v_unused_1435_ = lean_ctor_get(v_x_1385_, 0);
lean_dec(v_unused_1435_);
v___x_1397_ = v_x_1385_;
v_isShared_1398_ = v_isSharedCheck_1434_;
goto v_resetjp_1396_;
}
else
{
lean_dec(v_x_1385_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1434_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v_v_1399_; lean_object* v___x_1400_; lean_object* v_xs_x27_1401_; lean_object* v___y_1403_; 
v_v_1399_ = lean_array_fget(v_es_1390_, v_j_1393_);
v___x_1400_ = lean_box(0);
v_xs_x27_1401_ = lean_array_fset(v_es_1390_, v_j_1393_, v___x_1400_);
switch(lean_obj_tag(v_v_1399_))
{
case 0:
{
lean_object* v_key_1408_; lean_object* v_val_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1419_; 
v_key_1408_ = lean_ctor_get(v_v_1399_, 0);
v_val_1409_ = lean_ctor_get(v_v_1399_, 1);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_v_1399_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1411_ = v_v_1399_;
v_isShared_1412_ = v_isSharedCheck_1419_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_val_1409_);
lean_inc(v_key_1408_);
lean_dec(v_v_1399_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1419_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
uint8_t v___x_1413_; 
v___x_1413_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1388_, v_key_1408_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
lean_del_object(v___x_1411_);
v___x_1414_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1408_, v_val_1409_, v_x_1388_, v_x_1389_);
v___x_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
v___y_1403_ = v___x_1415_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1417_; 
lean_dec(v_val_1409_);
lean_dec(v_key_1408_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 1, v_x_1389_);
lean_ctor_set(v___x_1411_, 0, v_x_1388_);
v___x_1417_ = v___x_1411_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_x_1388_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_x_1389_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
v___y_1403_ = v___x_1417_;
goto v___jp_1402_;
}
}
}
}
case 1:
{
lean_object* v_node_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1432_; 
v_node_1420_ = lean_ctor_get(v_v_1399_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_v_1399_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1422_ = v_v_1399_;
v_isShared_1423_ = v_isSharedCheck_1432_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_node_1420_);
lean_dec(v_v_1399_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1432_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
size_t v___x_1424_; size_t v___x_1425_; size_t v___x_1426_; size_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1424_ = ((size_t)5ULL);
v___x_1425_ = lean_usize_shift_right(v_x_1386_, v___x_1424_);
v___x_1426_ = ((size_t)1ULL);
v___x_1427_ = lean_usize_add(v_x_1387_, v___x_1426_);
v___x_1428_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_node_1420_, v___x_1425_, v___x_1427_, v_x_1388_, v_x_1389_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1428_);
v___x_1430_ = v___x_1422_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
v___y_1403_ = v___x_1430_;
goto v___jp_1402_;
}
}
}
default: 
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v_x_1388_);
lean_ctor_set(v___x_1433_, 1, v_x_1389_);
v___y_1403_ = v___x_1433_;
goto v___jp_1402_;
}
}
v___jp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1404_ = lean_array_fset(v_xs_x27_1401_, v_j_1393_, v___y_1403_);
lean_dec(v_j_1393_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1404_);
v___x_1406_ = v___x_1397_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
else
{
lean_object* v_ks_1436_; lean_object* v_vs_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1457_; 
v_ks_1436_ = lean_ctor_get(v_x_1385_, 0);
v_vs_1437_ = lean_ctor_get(v_x_1385_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_x_1385_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1439_ = v_x_1385_;
v_isShared_1440_ = v_isSharedCheck_1457_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_vs_1437_);
lean_inc(v_ks_1436_);
lean_dec(v_x_1385_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1457_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_ks_1436_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_vs_1437_);
v___x_1442_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v_newNode_1443_; uint8_t v___y_1445_; size_t v___x_1451_; uint8_t v___x_1452_; 
v_newNode_1443_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v___x_1442_, v_x_1388_, v_x_1389_);
v___x_1451_ = ((size_t)7ULL);
v___x_1452_ = lean_usize_dec_le(v___x_1451_, v_x_1387_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1453_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1443_);
v___x_1454_ = lean_unsigned_to_nat(4u);
v___x_1455_ = lean_nat_dec_lt(v___x_1453_, v___x_1454_);
lean_dec(v___x_1453_);
v___y_1445_ = v___x_1455_;
goto v___jp_1444_;
}
else
{
v___y_1445_ = v___x_1452_;
goto v___jp_1444_;
}
v___jp_1444_:
{
if (v___y_1445_ == 0)
{
lean_object* v_ks_1446_; lean_object* v_vs_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_ks_1446_ = lean_ctor_get(v_newNode_1443_, 0);
lean_inc_ref(v_ks_1446_);
v_vs_1447_ = lean_ctor_get(v_newNode_1443_, 1);
lean_inc_ref(v_vs_1447_);
lean_dec_ref(v_newNode_1443_);
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0);
v___x_1450_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_x_1387_, v_ks_1446_, v_vs_1447_, v___x_1448_, v___x_1449_);
lean_dec_ref(v_vs_1447_);
lean_dec_ref(v_ks_1446_);
return v___x_1450_;
}
else
{
return v_newNode_1443_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1458_, lean_object* v_keys_1459_, lean_object* v_vals_1460_, lean_object* v_i_1461_, lean_object* v_entries_1462_){
_start:
{
lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = lean_array_get_size(v_keys_1459_);
v___x_1464_ = lean_nat_dec_lt(v_i_1461_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_dec(v_i_1461_);
return v_entries_1462_;
}
else
{
lean_object* v_k_1465_; lean_object* v_v_1466_; uint64_t v___x_1467_; size_t v_h_1468_; size_t v___x_1469_; lean_object* v___x_1470_; size_t v___x_1471_; size_t v___x_1472_; size_t v___x_1473_; size_t v_h_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v_k_1465_ = lean_array_fget_borrowed(v_keys_1459_, v_i_1461_);
v_v_1466_ = lean_array_fget_borrowed(v_vals_1460_, v_i_1461_);
v___x_1467_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1465_);
v_h_1468_ = lean_uint64_to_usize(v___x_1467_);
v___x_1469_ = ((size_t)5ULL);
v___x_1470_ = lean_unsigned_to_nat(1u);
v___x_1471_ = ((size_t)1ULL);
v___x_1472_ = lean_usize_sub(v_depth_1458_, v___x_1471_);
v___x_1473_ = lean_usize_mul(v___x_1469_, v___x_1472_);
v_h_1474_ = lean_usize_shift_right(v_h_1468_, v___x_1473_);
v___x_1475_ = lean_nat_add(v_i_1461_, v___x_1470_);
lean_dec(v_i_1461_);
lean_inc(v_v_1466_);
lean_inc(v_k_1465_);
v___x_1476_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_entries_1462_, v_h_1474_, v_depth_1458_, v_k_1465_, v_v_1466_);
v_i_1461_ = v___x_1475_;
v_entries_1462_ = v___x_1476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1478_, lean_object* v_keys_1479_, lean_object* v_vals_1480_, lean_object* v_i_1481_, lean_object* v_entries_1482_){
_start:
{
size_t v_depth_boxed_1483_; lean_object* v_res_1484_; 
v_depth_boxed_1483_ = lean_unbox_usize(v_depth_1478_);
lean_dec(v_depth_1478_);
v_res_1484_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1483_, v_keys_1479_, v_vals_1480_, v_i_1481_, v_entries_1482_);
lean_dec_ref(v_vals_1480_);
lean_dec_ref(v_keys_1479_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(lean_object* v_x_1485_, lean_object* v_x_1486_, lean_object* v_x_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_){
_start:
{
size_t v_x_7232__boxed_1490_; size_t v_x_7233__boxed_1491_; lean_object* v_res_1492_; 
v_x_7232__boxed_1490_ = lean_unbox_usize(v_x_1486_);
lean_dec(v_x_1486_);
v_x_7233__boxed_1491_ = lean_unbox_usize(v_x_1487_);
lean_dec(v_x_1487_);
v_res_1492_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1485_, v_x_7232__boxed_1490_, v_x_7233__boxed_1491_, v_x_1488_, v_x_1489_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(lean_object* v_x_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_){
_start:
{
uint64_t v___x_1496_; size_t v___x_1497_; size_t v___x_1498_; lean_object* v___x_1499_; 
v___x_1496_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1494_);
v___x_1497_ = lean_uint64_to_usize(v___x_1496_);
v___x_1498_ = ((size_t)1ULL);
v___x_1499_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1493_, v___x_1497_, v___x_1498_, v_x_1494_, v_x_1495_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(lean_object* v_e_1500_, lean_object* v_a_1501_, lean_object* v_s_1502_){
_start:
{
lean_object* v_rings_1503_; lean_object* v_typeIdOf_1504_; lean_object* v_exprToRingId_1505_; lean_object* v_semirings_1506_; lean_object* v_stypeIdOf_1507_; lean_object* v_exprToSemiringId_1508_; lean_object* v_ncRings_1509_; lean_object* v_exprToNCRingId_1510_; lean_object* v_nctypeIdOf_1511_; lean_object* v_ncSemirings_1512_; lean_object* v_exprToNCSemiringId_1513_; lean_object* v_ncstypeIdOf_1514_; lean_object* v_steps_1515_; uint8_t v_reportedMaxDegreeIssue_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1524_; 
v_rings_1503_ = lean_ctor_get(v_s_1502_, 0);
v_typeIdOf_1504_ = lean_ctor_get(v_s_1502_, 1);
v_exprToRingId_1505_ = lean_ctor_get(v_s_1502_, 2);
v_semirings_1506_ = lean_ctor_get(v_s_1502_, 3);
v_stypeIdOf_1507_ = lean_ctor_get(v_s_1502_, 4);
v_exprToSemiringId_1508_ = lean_ctor_get(v_s_1502_, 5);
v_ncRings_1509_ = lean_ctor_get(v_s_1502_, 6);
v_exprToNCRingId_1510_ = lean_ctor_get(v_s_1502_, 7);
v_nctypeIdOf_1511_ = lean_ctor_get(v_s_1502_, 8);
v_ncSemirings_1512_ = lean_ctor_get(v_s_1502_, 9);
v_exprToNCSemiringId_1513_ = lean_ctor_get(v_s_1502_, 10);
v_ncstypeIdOf_1514_ = lean_ctor_get(v_s_1502_, 11);
v_steps_1515_ = lean_ctor_get(v_s_1502_, 12);
v_reportedMaxDegreeIssue_1516_ = lean_ctor_get_uint8(v_s_1502_, sizeof(void*)*13);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_s_1502_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1518_ = v_s_1502_;
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_steps_1515_);
lean_inc(v_ncstypeIdOf_1514_);
lean_inc(v_exprToNCSemiringId_1513_);
lean_inc(v_ncSemirings_1512_);
lean_inc(v_nctypeIdOf_1511_);
lean_inc(v_exprToNCRingId_1510_);
lean_inc(v_ncRings_1509_);
lean_inc(v_exprToSemiringId_1508_);
lean_inc(v_stypeIdOf_1507_);
lean_inc(v_semirings_1506_);
lean_inc(v_exprToRingId_1505_);
lean_inc(v_typeIdOf_1504_);
lean_inc(v_rings_1503_);
lean_dec(v_s_1502_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
lean_inc(v_a_1501_);
v___x_1520_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_exprToSemiringId_1508_, v_e_1500_, v_a_1501_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 5, v___x_1520_);
v___x_1522_ = v___x_1518_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_rings_1503_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_typeIdOf_1504_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_exprToRingId_1505_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_semirings_1506_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v_stypeIdOf_1507_);
lean_ctor_set(v_reuseFailAlloc_1523_, 5, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1523_, 6, v_ncRings_1509_);
lean_ctor_set(v_reuseFailAlloc_1523_, 7, v_exprToNCRingId_1510_);
lean_ctor_set(v_reuseFailAlloc_1523_, 8, v_nctypeIdOf_1511_);
lean_ctor_set(v_reuseFailAlloc_1523_, 9, v_ncSemirings_1512_);
lean_ctor_set(v_reuseFailAlloc_1523_, 10, v_exprToNCSemiringId_1513_);
lean_ctor_set(v_reuseFailAlloc_1523_, 11, v_ncstypeIdOf_1514_);
lean_ctor_set(v_reuseFailAlloc_1523_, 12, v_steps_1515_);
lean_ctor_set_uint8(v_reuseFailAlloc_1523_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1516_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(lean_object* v_e_1525_, lean_object* v_a_1526_, lean_object* v_s_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(v_e_1525_, v_a_1526_, v_s_1527_);
lean_dec(v_a_1526_);
return v_res_1528_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0));
v___x_1531_ = l_Lean_stringToMessageData(v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object* v_e_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(v_e_1532_, v_a_1534_, v_a_1539_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
if (lean_obj_tag(v_a_1546_) == 1)
{
lean_object* v_val_1547_; uint8_t v___x_1548_; 
v_val_1547_ = lean_ctor_get(v_a_1546_, 0);
lean_inc(v_val_1547_);
lean_dec_ref_known(v_a_1546_, 1);
v___x_1548_ = lean_nat_dec_eq(v_val_1547_, v_a_1533_);
lean_dec(v_val_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1535_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; uint8_t v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1551_ = lean_unbox(v_a_1550_);
lean_dec(v_a_1550_);
if (v___x_1551_ == 0)
{
lean_dec_ref(v_e_1532_);
goto v___jp_1542_;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1552_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1);
v___x_1553_ = l_Lean_indentExpr(v_e_1532_);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = l_Lean_Meta_Sym_reportIssue(v___x_1554_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_dec_ref_known(v___x_1555_, 1);
goto v___jp_1542_;
}
else
{
return v___x_1555_;
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec_ref(v_e_1532_);
v_a_1556_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1549_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1549_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_dec_ref(v_e_1532_);
goto v___jp_1542_;
}
}
else
{
lean_object* v___f_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec(v_a_1546_);
lean_inc(v_a_1533_);
v___f_1564_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1564_, 0, v_e_1532_);
lean_closure_set(v___f_1564_, 1, v_a_1533_);
v___x_1565_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1566_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1565_, v___f_1564_, v_a_1534_);
return v___x_1566_;
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec_ref(v_e_1532_);
v_a_1567_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1545_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1545_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
v___jp_1542_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = lean_box(0);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(lean_object* v_e_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
lean_dec(v_a_1577_);
lean_dec(v_a_1576_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object* v_e_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1586_, v_a_1587_, v_a_1588_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(lean_object* v_e_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec(v_a_1601_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(lean_object* v_00_u03b2_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_, lean_object* v_x_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_x_1615_, v_x_1616_, v_x_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(lean_object* v_00_u03b2_1619_, lean_object* v_x_1620_, size_t v_x_1621_, size_t v_x_1622_, lean_object* v_x_1623_, lean_object* v_x_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_1620_, v_x_1621_, v_x_1622_, v_x_1623_, v_x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
size_t v_x_7511__boxed_1632_; size_t v_x_7512__boxed_1633_; lean_object* v_res_1634_; 
v_x_7511__boxed_1632_ = lean_unbox_usize(v_x_1628_);
lean_dec(v_x_1628_);
v_x_7512__boxed_1633_ = lean_unbox_usize(v_x_1629_);
lean_dec(v_x_1629_);
v_res_1634_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(v_00_u03b2_1626_, v_x_1627_, v_x_7511__boxed_1632_, v_x_7512__boxed_1633_, v_x_1630_, v_x_1631_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1635_, lean_object* v_n_1636_, lean_object* v_k_1637_, lean_object* v_v_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v_n_1636_, v_k_1637_, v_v_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1640_, size_t v_depth_1641_, lean_object* v_keys_1642_, lean_object* v_vals_1643_, lean_object* v_heq_1644_, lean_object* v_i_1645_, lean_object* v_entries_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_1641_, v_keys_1642_, v_vals_1643_, v_i_1645_, v_entries_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1648_, lean_object* v_depth_1649_, lean_object* v_keys_1650_, lean_object* v_vals_1651_, lean_object* v_heq_1652_, lean_object* v_i_1653_, lean_object* v_entries_1654_){
_start:
{
size_t v_depth_boxed_1655_; lean_object* v_res_1656_; 
v_depth_boxed_1655_ = lean_unbox_usize(v_depth_1649_);
lean_dec(v_depth_1649_);
v_res_1656_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_1648_, v_depth_boxed_1655_, v_keys_1650_, v_vals_1651_, v_heq_1652_, v_i_1653_, v_entries_1654_);
lean_dec_ref(v_vals_1651_);
lean_dec_ref(v_keys_1650_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1657_, lean_object* v_x_1658_, lean_object* v_x_1659_, lean_object* v_x_1660_, lean_object* v_x_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1658_, v_x_1659_, v_x_1660_, v_x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(lean_object* v_e_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1663_, v___y_1664_, v___y_1665_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(lean_object* v_e_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(v_e_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec(v___y_1678_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(lean_object* v_e_1693_, lean_object* v___f_1694_, lean_object* v___f_1695_, lean_object* v_size_1696_, lean_object* v_s_1697_){
_start:
{
lean_object* v_id_1698_; lean_object* v_type_1699_; lean_object* v_u_1700_; lean_object* v_semiringInst_1701_; lean_object* v_addFn_x3f_1702_; lean_object* v_mulFn_x3f_1703_; lean_object* v_powFn_x3f_1704_; lean_object* v_natCastFn_x3f_1705_; lean_object* v_denote_1706_; lean_object* v_vars_1707_; lean_object* v_varMap_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1717_; 
v_id_1698_ = lean_ctor_get(v_s_1697_, 0);
v_type_1699_ = lean_ctor_get(v_s_1697_, 1);
v_u_1700_ = lean_ctor_get(v_s_1697_, 2);
v_semiringInst_1701_ = lean_ctor_get(v_s_1697_, 3);
v_addFn_x3f_1702_ = lean_ctor_get(v_s_1697_, 4);
v_mulFn_x3f_1703_ = lean_ctor_get(v_s_1697_, 5);
v_powFn_x3f_1704_ = lean_ctor_get(v_s_1697_, 6);
v_natCastFn_x3f_1705_ = lean_ctor_get(v_s_1697_, 7);
v_denote_1706_ = lean_ctor_get(v_s_1697_, 8);
v_vars_1707_ = lean_ctor_get(v_s_1697_, 9);
v_varMap_1708_ = lean_ctor_get(v_s_1697_, 10);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_s_1697_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1710_ = v_s_1697_;
v_isShared_1711_ = v_isSharedCheck_1717_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_varMap_1708_);
lean_inc(v_vars_1707_);
lean_inc(v_denote_1706_);
lean_inc(v_natCastFn_x3f_1705_);
lean_inc(v_powFn_x3f_1704_);
lean_inc(v_mulFn_x3f_1703_);
lean_inc(v_addFn_x3f_1702_);
lean_inc(v_semiringInst_1701_);
lean_inc(v_u_1700_);
lean_inc(v_type_1699_);
lean_inc(v_id_1698_);
lean_dec(v_s_1697_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1717_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
lean_inc_ref(v_e_1693_);
v___x_1712_ = l_Lean_PersistentArray_push___redArg(v_vars_1707_, v_e_1693_);
v___x_1713_ = l_Lean_PersistentHashMap_insert___redArg(v___f_1694_, v___f_1695_, v_varMap_1708_, v_e_1693_, v_size_1696_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 10, v___x_1713_);
lean_ctor_set(v___x_1710_, 9, v___x_1712_);
v___x_1715_ = v___x_1710_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_id_1698_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_type_1699_);
lean_ctor_set(v_reuseFailAlloc_1716_, 2, v_u_1700_);
lean_ctor_set(v_reuseFailAlloc_1716_, 3, v_semiringInst_1701_);
lean_ctor_set(v_reuseFailAlloc_1716_, 4, v_addFn_x3f_1702_);
lean_ctor_set(v_reuseFailAlloc_1716_, 5, v_mulFn_x3f_1703_);
lean_ctor_set(v_reuseFailAlloc_1716_, 6, v_powFn_x3f_1704_);
lean_ctor_set(v_reuseFailAlloc_1716_, 7, v_natCastFn_x3f_1705_);
lean_ctor_set(v_reuseFailAlloc_1716_, 8, v_denote_1706_);
lean_ctor_set(v_reuseFailAlloc_1716_, 9, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1716_, 10, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(lean_object* v_toPure_1718_, lean_object* v_size_1719_, lean_object* v_____r_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_apply_2(v_toPure_1718_, lean_box(0), v_size_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(lean_object* v_e_1722_, lean_object* v_inst_1723_, lean_object* v_toBind_1724_, lean_object* v___f_1725_, lean_object* v_____r_1726_){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1727_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1728_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_1728_, 0, lean_box(0));
lean_closure_set(v___x_1728_, 1, v___x_1727_);
lean_closure_set(v___x_1728_, 2, v_e_1722_);
v___x_1729_ = lean_apply_2(v_inst_1723_, lean_box(0), v___x_1728_);
v___x_1730_ = lean_apply_4(v_toBind_1724_, lean_box(0), lean_box(0), v___x_1729_, v___f_1725_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(lean_object* v_inst_1731_, lean_object* v_e_1732_, lean_object* v_toBind_1733_, lean_object* v___f_1734_, lean_object* v_____r_1735_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_apply_1(v_inst_1731_, v_e_1732_);
v___x_1737_ = lean_apply_4(v_toBind_1733_, lean_box(0), lean_box(0), v___x_1736_, v___f_1734_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(lean_object* v___f_1738_, lean_object* v___f_1739_, lean_object* v_e_1740_, lean_object* v_toPure_1741_, lean_object* v_inst_1742_, lean_object* v_toBind_1743_, lean_object* v_inst_1744_, lean_object* v_modifySemiring_1745_, lean_object* v_s_1746_){
_start:
{
lean_object* v_vars_1747_; lean_object* v_varMap_1748_; lean_object* v___x_1749_; 
v_vars_1747_ = lean_ctor_get(v_s_1746_, 9);
lean_inc_ref(v_vars_1747_);
v_varMap_1748_ = lean_ctor_get(v_s_1746_, 10);
lean_inc_ref(v_varMap_1748_);
lean_dec_ref(v_s_1746_);
lean_inc_ref(v_e_1740_);
lean_inc_ref(v___f_1739_);
lean_inc_ref(v___f_1738_);
v___x_1749_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_1738_, v___f_1739_, v_varMap_1748_, v_e_1740_);
lean_dec_ref(v_varMap_1748_);
if (lean_obj_tag(v___x_1749_) == 1)
{
lean_object* v_val_1750_; lean_object* v___x_1751_; 
lean_dec_ref(v_vars_1747_);
lean_dec(v_modifySemiring_1745_);
lean_dec(v_inst_1744_);
lean_dec(v_toBind_1743_);
lean_dec(v_inst_1742_);
lean_dec_ref(v_e_1740_);
lean_dec_ref(v___f_1739_);
lean_dec_ref(v___f_1738_);
v_val_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_val_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = lean_apply_2(v_toPure_1741_, lean_box(0), v_val_1750_);
return v___x_1751_;
}
else
{
lean_object* v_size_1752_; lean_object* v___f_1753_; lean_object* v___f_1754_; lean_object* v___f_1755_; lean_object* v___f_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec(v___x_1749_);
v_size_1752_ = lean_ctor_get(v_vars_1747_, 2);
lean_inc_n(v_size_1752_, 2);
lean_dec_ref(v_vars_1747_);
lean_inc_ref_n(v_e_1740_, 2);
v___f_1753_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1753_, 0, v_e_1740_);
lean_closure_set(v___f_1753_, 1, v___f_1738_);
lean_closure_set(v___f_1753_, 2, v___f_1739_);
lean_closure_set(v___f_1753_, 3, v_size_1752_);
v___f_1754_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1754_, 0, v_toPure_1741_);
lean_closure_set(v___f_1754_, 1, v_size_1752_);
lean_inc_n(v_toBind_1743_, 2);
v___f_1755_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1755_, 0, v_e_1740_);
lean_closure_set(v___f_1755_, 1, v_inst_1742_);
lean_closure_set(v___f_1755_, 2, v_toBind_1743_);
lean_closure_set(v___f_1755_, 3, v___f_1754_);
v___f_1756_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1756_, 0, v_inst_1744_);
lean_closure_set(v___f_1756_, 1, v_e_1740_);
lean_closure_set(v___f_1756_, 2, v_toBind_1743_);
lean_closure_set(v___f_1756_, 3, v___f_1755_);
v___x_1757_ = lean_apply_1(v_modifySemiring_1745_, v___f_1753_);
v___x_1758_ = lean_apply_4(v_toBind_1743_, lean_box(0), lean_box(0), v___x_1757_, v___f_1756_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(lean_object* v_inst_1761_, lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_e_1765_){
_start:
{
lean_object* v_toApplicative_1766_; lean_object* v_toBind_1767_; lean_object* v_getSemiring_1768_; lean_object* v_modifySemiring_1769_; lean_object* v_toPure_1770_; lean_object* v___f_1771_; lean_object* v___f_1772_; lean_object* v___f_1773_; lean_object* v___x_1774_; 
v_toApplicative_1766_ = lean_ctor_get(v_inst_1762_, 0);
lean_inc_ref(v_toApplicative_1766_);
v_toBind_1767_ = lean_ctor_get(v_inst_1762_, 1);
lean_inc_n(v_toBind_1767_, 2);
lean_dec_ref(v_inst_1762_);
v_getSemiring_1768_ = lean_ctor_get(v_inst_1763_, 0);
lean_inc(v_getSemiring_1768_);
v_modifySemiring_1769_ = lean_ctor_get(v_inst_1763_, 1);
lean_inc(v_modifySemiring_1769_);
lean_dec_ref(v_inst_1763_);
v_toPure_1770_ = lean_ctor_get(v_toApplicative_1766_, 1);
lean_inc(v_toPure_1770_);
lean_dec_ref(v_toApplicative_1766_);
v___f_1771_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0));
v___f_1772_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1));
v___f_1773_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_1773_, 0, v___f_1771_);
lean_closure_set(v___f_1773_, 1, v___f_1772_);
lean_closure_set(v___f_1773_, 2, v_e_1765_);
lean_closure_set(v___f_1773_, 3, v_toPure_1770_);
lean_closure_set(v___f_1773_, 4, v_inst_1761_);
lean_closure_set(v___f_1773_, 5, v_toBind_1767_);
lean_closure_set(v___f_1773_, 6, v_inst_1764_);
lean_closure_set(v___f_1773_, 7, v_modifySemiring_1769_);
v___x_1774_ = lean_apply_4(v_toBind_1767_, lean_box(0), lean_box(0), v_getSemiring_1768_, v___f_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(lean_object* v_m_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_e_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(v_inst_1776_, v_inst_1777_, v_inst_1778_, v_inst_1779_, v_e_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(lean_object* v___y_1782_, lean_object* v_e_1783_, lean_object* v_size_1784_, lean_object* v_s_1785_){
_start:
{
lean_object* v_rings_1786_; lean_object* v_typeIdOf_1787_; lean_object* v_exprToRingId_1788_; lean_object* v_semirings_1789_; lean_object* v_stypeIdOf_1790_; lean_object* v_exprToSemiringId_1791_; lean_object* v_ncRings_1792_; lean_object* v_exprToNCRingId_1793_; lean_object* v_nctypeIdOf_1794_; lean_object* v_ncSemirings_1795_; lean_object* v_exprToNCSemiringId_1796_; lean_object* v_ncstypeIdOf_1797_; lean_object* v_steps_1798_; uint8_t v_reportedMaxDegreeIssue_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v_rings_1786_ = lean_ctor_get(v_s_1785_, 0);
v_typeIdOf_1787_ = lean_ctor_get(v_s_1785_, 1);
v_exprToRingId_1788_ = lean_ctor_get(v_s_1785_, 2);
v_semirings_1789_ = lean_ctor_get(v_s_1785_, 3);
v_stypeIdOf_1790_ = lean_ctor_get(v_s_1785_, 4);
v_exprToSemiringId_1791_ = lean_ctor_get(v_s_1785_, 5);
v_ncRings_1792_ = lean_ctor_get(v_s_1785_, 6);
v_exprToNCRingId_1793_ = lean_ctor_get(v_s_1785_, 7);
v_nctypeIdOf_1794_ = lean_ctor_get(v_s_1785_, 8);
v_ncSemirings_1795_ = lean_ctor_get(v_s_1785_, 9);
v_exprToNCSemiringId_1796_ = lean_ctor_get(v_s_1785_, 10);
v_ncstypeIdOf_1797_ = lean_ctor_get(v_s_1785_, 11);
v_steps_1798_ = lean_ctor_get(v_s_1785_, 12);
v_reportedMaxDegreeIssue_1799_ = lean_ctor_get_uint8(v_s_1785_, sizeof(void*)*13);
v___x_1800_ = lean_array_get_size(v_semirings_1789_);
v___x_1801_ = lean_nat_dec_lt(v___y_1782_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_dec(v_size_1784_);
lean_dec_ref(v_e_1783_);
return v_s_1785_;
}
else
{
lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1844_; 
lean_inc(v_steps_1798_);
lean_inc_ref(v_ncstypeIdOf_1797_);
lean_inc_ref(v_exprToNCSemiringId_1796_);
lean_inc_ref(v_ncSemirings_1795_);
lean_inc_ref(v_nctypeIdOf_1794_);
lean_inc_ref(v_exprToNCRingId_1793_);
lean_inc_ref(v_ncRings_1792_);
lean_inc_ref(v_exprToSemiringId_1791_);
lean_inc_ref(v_stypeIdOf_1790_);
lean_inc_ref(v_semirings_1789_);
lean_inc_ref(v_exprToRingId_1788_);
lean_inc_ref(v_typeIdOf_1787_);
lean_inc_ref(v_rings_1786_);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_s_1785_);
if (v_isSharedCheck_1844_ == 0)
{
lean_object* v_unused_1845_; lean_object* v_unused_1846_; lean_object* v_unused_1847_; lean_object* v_unused_1848_; lean_object* v_unused_1849_; lean_object* v_unused_1850_; lean_object* v_unused_1851_; lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; 
v_unused_1845_ = lean_ctor_get(v_s_1785_, 12);
lean_dec(v_unused_1845_);
v_unused_1846_ = lean_ctor_get(v_s_1785_, 11);
lean_dec(v_unused_1846_);
v_unused_1847_ = lean_ctor_get(v_s_1785_, 10);
lean_dec(v_unused_1847_);
v_unused_1848_ = lean_ctor_get(v_s_1785_, 9);
lean_dec(v_unused_1848_);
v_unused_1849_ = lean_ctor_get(v_s_1785_, 8);
lean_dec(v_unused_1849_);
v_unused_1850_ = lean_ctor_get(v_s_1785_, 7);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v_s_1785_, 6);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_s_1785_, 5);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v_s_1785_, 4);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_s_1785_, 3);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v_s_1785_, 2);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_s_1785_, 1);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_s_1785_, 0);
lean_dec(v_unused_1857_);
v___x_1803_ = v_s_1785_;
v_isShared_1804_ = v_isSharedCheck_1844_;
goto v_resetjp_1802_;
}
else
{
lean_dec(v_s_1785_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1844_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_v_1805_; lean_object* v_toSemiring_1806_; lean_object* v_ringId_1807_; lean_object* v_commSemiringInst_1808_; lean_object* v_addRightCancelInst_x3f_1809_; lean_object* v_toQFn_x3f_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1843_; 
v_v_1805_ = lean_array_fget(v_semirings_1789_, v___y_1782_);
v_toSemiring_1806_ = lean_ctor_get(v_v_1805_, 0);
v_ringId_1807_ = lean_ctor_get(v_v_1805_, 1);
v_commSemiringInst_1808_ = lean_ctor_get(v_v_1805_, 2);
v_addRightCancelInst_x3f_1809_ = lean_ctor_get(v_v_1805_, 3);
v_toQFn_x3f_1810_ = lean_ctor_get(v_v_1805_, 4);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_v_1805_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1812_ = v_v_1805_;
v_isShared_1813_ = v_isSharedCheck_1843_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_toQFn_x3f_1810_);
lean_inc(v_addRightCancelInst_x3f_1809_);
lean_inc(v_commSemiringInst_1808_);
lean_inc(v_ringId_1807_);
lean_inc(v_toSemiring_1806_);
lean_dec(v_v_1805_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1843_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v_id_1814_; lean_object* v_type_1815_; lean_object* v_u_1816_; lean_object* v_semiringInst_1817_; lean_object* v_addFn_x3f_1818_; lean_object* v_mulFn_x3f_1819_; lean_object* v_powFn_x3f_1820_; lean_object* v_natCastFn_x3f_1821_; lean_object* v_denote_1822_; lean_object* v_vars_1823_; lean_object* v_varMap_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1842_; 
v_id_1814_ = lean_ctor_get(v_toSemiring_1806_, 0);
v_type_1815_ = lean_ctor_get(v_toSemiring_1806_, 1);
v_u_1816_ = lean_ctor_get(v_toSemiring_1806_, 2);
v_semiringInst_1817_ = lean_ctor_get(v_toSemiring_1806_, 3);
v_addFn_x3f_1818_ = lean_ctor_get(v_toSemiring_1806_, 4);
v_mulFn_x3f_1819_ = lean_ctor_get(v_toSemiring_1806_, 5);
v_powFn_x3f_1820_ = lean_ctor_get(v_toSemiring_1806_, 6);
v_natCastFn_x3f_1821_ = lean_ctor_get(v_toSemiring_1806_, 7);
v_denote_1822_ = lean_ctor_get(v_toSemiring_1806_, 8);
v_vars_1823_ = lean_ctor_get(v_toSemiring_1806_, 9);
v_varMap_1824_ = lean_ctor_get(v_toSemiring_1806_, 10);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_toSemiring_1806_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1826_ = v_toSemiring_1806_;
v_isShared_1827_ = v_isSharedCheck_1842_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_varMap_1824_);
lean_inc(v_vars_1823_);
lean_inc(v_denote_1822_);
lean_inc(v_natCastFn_x3f_1821_);
lean_inc(v_powFn_x3f_1820_);
lean_inc(v_mulFn_x3f_1819_);
lean_inc(v_addFn_x3f_1818_);
lean_inc(v_semiringInst_1817_);
lean_inc(v_u_1816_);
lean_inc(v_type_1815_);
lean_inc(v_id_1814_);
lean_dec(v_toSemiring_1806_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1842_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v_xs_x27_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1828_ = lean_box(0);
v_xs_x27_1829_ = lean_array_fset(v_semirings_1789_, v___y_1782_, v___x_1828_);
lean_inc_ref(v_e_1783_);
v___x_1830_ = l_Lean_PersistentArray_push___redArg(v_vars_1823_, v_e_1783_);
v___x_1831_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_varMap_1824_, v_e_1783_, v_size_1784_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 10, v___x_1831_);
lean_ctor_set(v___x_1826_, 9, v___x_1830_);
v___x_1833_ = v___x_1826_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_id_1814_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_type_1815_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_u_1816_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_semiringInst_1817_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_addFn_x3f_1818_);
lean_ctor_set(v_reuseFailAlloc_1841_, 5, v_mulFn_x3f_1819_);
lean_ctor_set(v_reuseFailAlloc_1841_, 6, v_powFn_x3f_1820_);
lean_ctor_set(v_reuseFailAlloc_1841_, 7, v_natCastFn_x3f_1821_);
lean_ctor_set(v_reuseFailAlloc_1841_, 8, v_denote_1822_);
lean_ctor_set(v_reuseFailAlloc_1841_, 9, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1841_, 10, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1835_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1833_);
v___x_1835_ = v___x_1812_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_ringId_1807_);
lean_ctor_set(v_reuseFailAlloc_1840_, 2, v_commSemiringInst_1808_);
lean_ctor_set(v_reuseFailAlloc_1840_, 3, v_addRightCancelInst_x3f_1809_);
lean_ctor_set(v_reuseFailAlloc_1840_, 4, v_toQFn_x3f_1810_);
v___x_1835_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1836_ = lean_array_fset(v_xs_x27_1829_, v___y_1782_, v___x_1835_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 3, v___x_1836_);
v___x_1838_ = v___x_1803_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_rings_1786_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_typeIdOf_1787_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v_exprToRingId_1788_);
lean_ctor_set(v_reuseFailAlloc_1839_, 3, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1839_, 4, v_stypeIdOf_1790_);
lean_ctor_set(v_reuseFailAlloc_1839_, 5, v_exprToSemiringId_1791_);
lean_ctor_set(v_reuseFailAlloc_1839_, 6, v_ncRings_1792_);
lean_ctor_set(v_reuseFailAlloc_1839_, 7, v_exprToNCRingId_1793_);
lean_ctor_set(v_reuseFailAlloc_1839_, 8, v_nctypeIdOf_1794_);
lean_ctor_set(v_reuseFailAlloc_1839_, 9, v_ncSemirings_1795_);
lean_ctor_set(v_reuseFailAlloc_1839_, 10, v_exprToNCSemiringId_1796_);
lean_ctor_set(v_reuseFailAlloc_1839_, 11, v_ncstypeIdOf_1797_);
lean_ctor_set(v_reuseFailAlloc_1839_, 12, v_steps_1798_);
lean_ctor_set_uint8(v_reuseFailAlloc_1839_, sizeof(void*)*13, v_reportedMaxDegreeIssue_1799_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed(lean_object* v___y_1858_, lean_object* v_e_1859_, lean_object* v_size_1860_, lean_object* v_s_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(v___y_1858_, v_e_1859_, v_size_1860_, v_s_1861_);
lean_dec(v___y_1858_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(lean_object* v_e_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1927_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1927_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1927_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_toSemiring_1881_; lean_object* v_vars_1882_; lean_object* v_varMap_1883_; lean_object* v___x_1884_; 
v_toSemiring_1881_ = lean_ctor_get(v_a_1877_, 0);
lean_inc_ref(v_toSemiring_1881_);
lean_dec(v_a_1877_);
v_vars_1882_ = lean_ctor_get(v_toSemiring_1881_, 9);
lean_inc_ref(v_vars_1882_);
v_varMap_1883_ = lean_ctor_get(v_toSemiring_1881_, 10);
lean_inc_ref(v_varMap_1883_);
lean_dec_ref(v_toSemiring_1881_);
v___x_1884_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_varMap_1883_, v_e_1863_);
lean_dec_ref(v_varMap_1883_);
if (lean_obj_tag(v___x_1884_) == 1)
{
lean_object* v_val_1885_; lean_object* v___x_1887_; 
lean_dec_ref(v_vars_1882_);
lean_dec_ref(v_e_1863_);
v_val_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_val_1885_);
lean_dec_ref_known(v___x_1884_, 1);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v_val_1885_);
v___x_1887_ = v___x_1879_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_val_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
else
{
lean_object* v_size_1889_; lean_object* v___f_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
lean_dec(v___x_1884_);
lean_del_object(v___x_1879_);
v_size_1889_ = lean_ctor_get(v_vars_1882_, 2);
lean_inc_n(v_size_1889_, 2);
lean_dec_ref(v_vars_1882_);
lean_inc_ref(v_e_1863_);
lean_inc(v___y_1864_);
v___f_1890_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1890_, 0, v___y_1864_);
lean_closure_set(v___f_1890_, 1, v_e_1863_);
lean_closure_set(v___f_1890_, 2, v_size_1889_);
v___x_1891_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_1892_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1891_, v___f_1890_, v___y_1865_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v___x_1893_; 
lean_dec_ref_known(v___x_1892_, 1);
lean_inc_ref(v_e_1863_);
v___x_1893_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_1863_, v___y_1864_, v___y_1865_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v___x_1894_; 
lean_dec_ref_known(v___x_1893_, 1);
v___x_1894_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1891_, v_e_1863_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; 
v_unused_1902_ = lean_ctor_get(v___x_1894_, 0);
lean_dec(v_unused_1902_);
v___x_1896_ = v___x_1894_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v___x_1894_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v_size_1889_);
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_size_1889_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec(v_size_1889_);
v_a_1903_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1894_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1894_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v_size_1889_);
lean_dec_ref(v_e_1863_);
v_a_1911_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1893_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1893_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v_size_1889_);
lean_dec_ref(v_e_1863_);
v_a_1919_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1892_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1892_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec_ref(v_e_1863_);
v_a_1928_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1876_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1876_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___boxed(lean_object* v_e_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec(v___y_1937_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar(lean_object* v_e_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar___boxed(lean_object* v_e_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVar(v_e_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec(v_a_1966_);
lean_dec(v_a_1965_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(lean_object* v_a_1978_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_nat_to_int(v_a_1978_);
return v___x_1979_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(lean_object* v_msg_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___x_1994_; lean_object* v___f_1995_; lean_object* v___x_40218__overap_1996_; lean_object* v___x_1997_; 
v___x_1994_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0);
v___f_1995_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1995_, 0, v___x_1994_);
v___x_40218__overap_1996_ = lean_panic_fn_borrowed(v___f_1995_, v_msg_1981_);
lean_dec_ref(v___f_1995_);
lean_inc(v___y_1992_);
lean_inc_ref(v___y_1991_);
lean_inc(v___y_1990_);
lean_inc_ref(v___y_1989_);
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1987_);
lean_inc(v___y_1986_);
lean_inc_ref(v___y_1985_);
lean_inc(v___y_1984_);
lean_inc(v___y_1983_);
lean_inc(v___y_1982_);
v___x_1997_ = lean_apply_12(v___x_40218__overap_1996_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, lean_box(0));
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(lean_object* v_msg_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v_msg_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec(v___y_1999_);
return v_res_2011_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0));
v___x_2014_ = l_Lean_stringToMessageData(v___x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(lean_object* v_type_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___x_2021_; 
lean_inc_ref(v_type_2015_);
v___x_2021_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2034_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2034_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2034_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
if (lean_obj_tag(v_a_2022_) == 1)
{
lean_object* v_val_2026_; lean_object* v___x_2028_; 
lean_dec_ref(v_type_2015_);
v_val_2026_ = lean_ctor_get(v_a_2022_, 0);
lean_inc(v_val_2026_);
lean_dec_ref_known(v_a_2022_, 1);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v_val_2026_);
v___x_2028_ = v___x_2024_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_val_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_del_object(v___x_2024_);
lean_dec(v_a_2022_);
v___x_2030_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1);
v___x_2031_ = l_Lean_indentExpr(v_type_2015_);
v___x_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_2032_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
return v___x_2033_;
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v_type_2015_);
v_a_2035_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2021_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2021_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_type_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(lean_object* v_type_2050_, lean_object* v_u_2051_, lean_object* v_instDeclName_2052_, lean_object* v_declName_2053_, lean_object* v_expectedInst_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2067_ = lean_box(0);
lean_inc_n(v_u_2051_, 2);
v___x_2068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2068_, 0, v_u_2051_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_u_2051_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2070_, 0, v_u_2051_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
lean_inc_ref(v___x_2070_);
v___x_2071_ = l_Lean_mkConst(v_instDeclName_2052_, v___x_2070_);
lean_inc_ref_n(v_type_2050_, 3);
v___x_2072_ = l_Lean_mkApp3(v___x_2071_, v_type_2050_, v_type_2050_, v_type_2050_);
v___x_2073_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2072_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2075_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc_n(v_a_2074_, 2);
lean_dec_ref_known(v___x_2073_, 1);
lean_inc(v_declName_2053_);
v___x_2075_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2053_, v_a_2074_, v_expectedInst_2054_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec_ref_known(v___x_2075_, 1);
v___x_2076_ = l_Lean_mkConst(v_declName_2053_, v___x_2070_);
lean_inc_ref_n(v_type_2050_, 2);
v___x_2077_ = l_Lean_mkApp4(v___x_2076_, v_type_2050_, v_type_2050_, v_type_2050_, v_a_2074_);
v___x_2078_ = l_Lean_Meta_Sym_canon(v___x_2077_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2080_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2078_, 1);
v___x_2080_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2079_, v___y_2061_);
return v___x_2080_;
}
else
{
return v___x_2078_;
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_a_2074_);
lean_dec_ref_known(v___x_2070_, 2);
lean_dec(v_declName_2053_);
lean_dec_ref(v_type_2050_);
v_a_2081_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2075_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2075_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2070_, 2);
lean_dec_ref(v_expectedInst_2054_);
lean_dec(v_declName_2053_);
lean_dec_ref(v_type_2050_);
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v_type_2089_ = _args[0];
lean_object* v_u_2090_ = _args[1];
lean_object* v_instDeclName_2091_ = _args[2];
lean_object* v_declName_2092_ = _args[3];
lean_object* v_expectedInst_2093_ = _args[4];
lean_object* v___y_2094_ = _args[5];
lean_object* v___y_2095_ = _args[6];
lean_object* v___y_2096_ = _args[7];
lean_object* v___y_2097_ = _args[8];
lean_object* v___y_2098_ = _args[9];
lean_object* v___y_2099_ = _args[10];
lean_object* v___y_2100_ = _args[11];
lean_object* v___y_2101_ = _args[12];
lean_object* v___y_2102_ = _args[13];
lean_object* v___y_2103_ = _args[14];
lean_object* v___y_2104_ = _args[15];
lean_object* v___y_2105_ = _args[16];
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2089_, v_u_2090_, v_instDeclName_2091_, v_declName_2092_, v_expectedInst_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec(v___y_2094_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(lean_object* v_a_2107_, lean_object* v_s_2108_){
_start:
{
lean_object* v_toRing_2109_; lean_object* v_invFn_x3f_2110_; lean_object* v_semiringId_x3f_2111_; lean_object* v_commSemiringInst_2112_; lean_object* v_commRingInst_2113_; lean_object* v_noZeroDivInst_x3f_2114_; lean_object* v_fieldInst_x3f_2115_; lean_object* v_powIdentityInst_x3f_2116_; lean_object* v_denoteEntries_2117_; lean_object* v_nextId_2118_; lean_object* v_steps_2119_; lean_object* v_queue_2120_; lean_object* v_basis_2121_; lean_object* v_diseqs_2122_; uint8_t v_recheck_2123_; lean_object* v_invSet_2124_; lean_object* v_powIdentityVarCount_2125_; lean_object* v_numEq0_x3f_2126_; uint8_t v_numEq0Updated_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2159_; 
v_toRing_2109_ = lean_ctor_get(v_s_2108_, 0);
v_invFn_x3f_2110_ = lean_ctor_get(v_s_2108_, 1);
v_semiringId_x3f_2111_ = lean_ctor_get(v_s_2108_, 2);
v_commSemiringInst_2112_ = lean_ctor_get(v_s_2108_, 3);
v_commRingInst_2113_ = lean_ctor_get(v_s_2108_, 4);
v_noZeroDivInst_x3f_2114_ = lean_ctor_get(v_s_2108_, 5);
v_fieldInst_x3f_2115_ = lean_ctor_get(v_s_2108_, 6);
v_powIdentityInst_x3f_2116_ = lean_ctor_get(v_s_2108_, 7);
v_denoteEntries_2117_ = lean_ctor_get(v_s_2108_, 8);
v_nextId_2118_ = lean_ctor_get(v_s_2108_, 9);
v_steps_2119_ = lean_ctor_get(v_s_2108_, 10);
v_queue_2120_ = lean_ctor_get(v_s_2108_, 11);
v_basis_2121_ = lean_ctor_get(v_s_2108_, 12);
v_diseqs_2122_ = lean_ctor_get(v_s_2108_, 13);
v_recheck_2123_ = lean_ctor_get_uint8(v_s_2108_, sizeof(void*)*17);
v_invSet_2124_ = lean_ctor_get(v_s_2108_, 14);
v_powIdentityVarCount_2125_ = lean_ctor_get(v_s_2108_, 15);
v_numEq0_x3f_2126_ = lean_ctor_get(v_s_2108_, 16);
v_numEq0Updated_2127_ = lean_ctor_get_uint8(v_s_2108_, sizeof(void*)*17 + 1);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_s_2108_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2129_ = v_s_2108_;
v_isShared_2130_ = v_isSharedCheck_2159_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_numEq0_x3f_2126_);
lean_inc(v_powIdentityVarCount_2125_);
lean_inc(v_invSet_2124_);
lean_inc(v_diseqs_2122_);
lean_inc(v_basis_2121_);
lean_inc(v_queue_2120_);
lean_inc(v_steps_2119_);
lean_inc(v_nextId_2118_);
lean_inc(v_denoteEntries_2117_);
lean_inc(v_powIdentityInst_x3f_2116_);
lean_inc(v_fieldInst_x3f_2115_);
lean_inc(v_noZeroDivInst_x3f_2114_);
lean_inc(v_commRingInst_2113_);
lean_inc(v_commSemiringInst_2112_);
lean_inc(v_semiringId_x3f_2111_);
lean_inc(v_invFn_x3f_2110_);
lean_inc(v_toRing_2109_);
lean_dec(v_s_2108_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2159_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_id_2131_; lean_object* v_type_2132_; lean_object* v_u_2133_; lean_object* v_ringInst_2134_; lean_object* v_semiringInst_2135_; lean_object* v_charInst_x3f_2136_; lean_object* v_addFn_x3f_2137_; lean_object* v_subFn_x3f_2138_; lean_object* v_negFn_x3f_2139_; lean_object* v_powFn_x3f_2140_; lean_object* v_intCastFn_x3f_2141_; lean_object* v_natCastFn_x3f_2142_; lean_object* v_one_x3f_2143_; lean_object* v_vars_2144_; lean_object* v_varMap_2145_; lean_object* v_denote_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2157_; 
v_id_2131_ = lean_ctor_get(v_toRing_2109_, 0);
v_type_2132_ = lean_ctor_get(v_toRing_2109_, 1);
v_u_2133_ = lean_ctor_get(v_toRing_2109_, 2);
v_ringInst_2134_ = lean_ctor_get(v_toRing_2109_, 3);
v_semiringInst_2135_ = lean_ctor_get(v_toRing_2109_, 4);
v_charInst_x3f_2136_ = lean_ctor_get(v_toRing_2109_, 5);
v_addFn_x3f_2137_ = lean_ctor_get(v_toRing_2109_, 6);
v_subFn_x3f_2138_ = lean_ctor_get(v_toRing_2109_, 8);
v_negFn_x3f_2139_ = lean_ctor_get(v_toRing_2109_, 9);
v_powFn_x3f_2140_ = lean_ctor_get(v_toRing_2109_, 10);
v_intCastFn_x3f_2141_ = lean_ctor_get(v_toRing_2109_, 11);
v_natCastFn_x3f_2142_ = lean_ctor_get(v_toRing_2109_, 12);
v_one_x3f_2143_ = lean_ctor_get(v_toRing_2109_, 13);
v_vars_2144_ = lean_ctor_get(v_toRing_2109_, 14);
v_varMap_2145_ = lean_ctor_get(v_toRing_2109_, 15);
v_denote_2146_ = lean_ctor_get(v_toRing_2109_, 16);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_toRing_2109_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; 
v_unused_2158_ = lean_ctor_get(v_toRing_2109_, 7);
lean_dec(v_unused_2158_);
v___x_2148_ = v_toRing_2109_;
v_isShared_2149_ = v_isSharedCheck_2157_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_denote_2146_);
lean_inc(v_varMap_2145_);
lean_inc(v_vars_2144_);
lean_inc(v_one_x3f_2143_);
lean_inc(v_natCastFn_x3f_2142_);
lean_inc(v_intCastFn_x3f_2141_);
lean_inc(v_powFn_x3f_2140_);
lean_inc(v_negFn_x3f_2139_);
lean_inc(v_subFn_x3f_2138_);
lean_inc(v_addFn_x3f_2137_);
lean_inc(v_charInst_x3f_2136_);
lean_inc(v_semiringInst_2135_);
lean_inc(v_ringInst_2134_);
lean_inc(v_u_2133_);
lean_inc(v_type_2132_);
lean_inc(v_id_2131_);
lean_dec(v_toRing_2109_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2157_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2150_, 0, v_a_2107_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 7, v___x_2150_);
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_id_2131_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_type_2132_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_u_2133_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v_ringInst_2134_);
lean_ctor_set(v_reuseFailAlloc_2156_, 4, v_semiringInst_2135_);
lean_ctor_set(v_reuseFailAlloc_2156_, 5, v_charInst_x3f_2136_);
lean_ctor_set(v_reuseFailAlloc_2156_, 6, v_addFn_x3f_2137_);
lean_ctor_set(v_reuseFailAlloc_2156_, 7, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2156_, 8, v_subFn_x3f_2138_);
lean_ctor_set(v_reuseFailAlloc_2156_, 9, v_negFn_x3f_2139_);
lean_ctor_set(v_reuseFailAlloc_2156_, 10, v_powFn_x3f_2140_);
lean_ctor_set(v_reuseFailAlloc_2156_, 11, v_intCastFn_x3f_2141_);
lean_ctor_set(v_reuseFailAlloc_2156_, 12, v_natCastFn_x3f_2142_);
lean_ctor_set(v_reuseFailAlloc_2156_, 13, v_one_x3f_2143_);
lean_ctor_set(v_reuseFailAlloc_2156_, 14, v_vars_2144_);
lean_ctor_set(v_reuseFailAlloc_2156_, 15, v_varMap_2145_);
lean_ctor_set(v_reuseFailAlloc_2156_, 16, v_denote_2146_);
v___x_2152_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2152_);
v___x_2154_ = v___x_2129_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_invFn_x3f_2110_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_semiringId_x3f_2111_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v_commSemiringInst_2112_);
lean_ctor_set(v_reuseFailAlloc_2155_, 4, v_commRingInst_2113_);
lean_ctor_set(v_reuseFailAlloc_2155_, 5, v_noZeroDivInst_x3f_2114_);
lean_ctor_set(v_reuseFailAlloc_2155_, 6, v_fieldInst_x3f_2115_);
lean_ctor_set(v_reuseFailAlloc_2155_, 7, v_powIdentityInst_x3f_2116_);
lean_ctor_set(v_reuseFailAlloc_2155_, 8, v_denoteEntries_2117_);
lean_ctor_set(v_reuseFailAlloc_2155_, 9, v_nextId_2118_);
lean_ctor_set(v_reuseFailAlloc_2155_, 10, v_steps_2119_);
lean_ctor_set(v_reuseFailAlloc_2155_, 11, v_queue_2120_);
lean_ctor_set(v_reuseFailAlloc_2155_, 12, v_basis_2121_);
lean_ctor_set(v_reuseFailAlloc_2155_, 13, v_diseqs_2122_);
lean_ctor_set(v_reuseFailAlloc_2155_, 14, v_invSet_2124_);
lean_ctor_set(v_reuseFailAlloc_2155_, 15, v_powIdentityVarCount_2125_);
lean_ctor_set(v_reuseFailAlloc_2155_, 16, v_numEq0_x3f_2126_);
lean_ctor_set_uint8(v_reuseFailAlloc_2155_, sizeof(void*)*17, v_recheck_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2155_, sizeof(void*)*17 + 1, v_numEq0Updated_2127_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2216_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2216_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2216_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v_toRing_2177_; lean_object* v_mulFn_x3f_2178_; 
v_toRing_2177_ = lean_ctor_get(v_a_2173_, 0);
lean_inc_ref(v_toRing_2177_);
lean_dec(v_a_2173_);
v_mulFn_x3f_2178_ = lean_ctor_get(v_toRing_2177_, 7);
if (lean_obj_tag(v_mulFn_x3f_2178_) == 1)
{
lean_object* v_val_2179_; lean_object* v___x_2181_; 
lean_inc_ref(v_mulFn_x3f_2178_);
lean_dec_ref(v_toRing_2177_);
v_val_2179_ = lean_ctor_get(v_mulFn_x3f_2178_, 0);
lean_inc(v_val_2179_);
lean_dec_ref_known(v_mulFn_x3f_2178_, 1);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v_val_2179_);
v___x_2181_ = v___x_2175_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_val_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
else
{
lean_object* v_type_2183_; lean_object* v_u_2184_; lean_object* v_semiringInst_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v_expectedInst_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_del_object(v___x_2175_);
v_type_2183_ = lean_ctor_get(v_toRing_2177_, 1);
lean_inc_ref_n(v_type_2183_, 3);
v_u_2184_ = lean_ctor_get(v_toRing_2177_, 2);
lean_inc_n(v_u_2184_, 2);
v_semiringInst_2185_ = lean_ctor_get(v_toRing_2177_, 4);
lean_inc_ref(v_semiringInst_2185_);
lean_dec_ref(v_toRing_2177_);
v___x_2186_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1));
v___x_2187_ = lean_box(0);
v___x_2188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2188_, 0, v_u_2184_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
lean_inc_ref(v___x_2188_);
v___x_2189_ = l_Lean_mkConst(v___x_2186_, v___x_2188_);
v___x_2190_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3));
v___x_2191_ = l_Lean_mkConst(v___x_2190_, v___x_2188_);
v___x_2192_ = l_Lean_mkAppB(v___x_2191_, v_type_2183_, v_semiringInst_2185_);
v_expectedInst_2193_ = l_Lean_mkAppB(v___x_2189_, v_type_2183_, v___x_2192_);
v___x_2194_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5));
v___x_2195_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7));
v___x_2196_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2183_, v_u_2184_, v___x_2194_, v___x_2195_, v_expectedInst_2193_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___f_2198_; lean_object* v___x_2199_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc_n(v_a_2197_, 2);
lean_dec_ref_known(v___x_2196_, 1);
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2198_, 0, v_a_2197_);
v___x_2199_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2198_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; 
v_unused_2207_ = lean_ctor_get(v___x_2199_, 0);
lean_dec(v_unused_2207_);
v___x_2201_ = v___x_2199_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_dec(v___x_2199_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v_a_2197_);
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2197_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec(v_a_2197_);
v_a_2208_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2199_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2199_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
v_a_2217_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2172_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2172_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec(v___y_2225_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(lean_object* v_a_2238_, lean_object* v_s_2239_){
_start:
{
lean_object* v_toRing_2240_; lean_object* v_invFn_x3f_2241_; lean_object* v_semiringId_x3f_2242_; lean_object* v_commSemiringInst_2243_; lean_object* v_commRingInst_2244_; lean_object* v_noZeroDivInst_x3f_2245_; lean_object* v_fieldInst_x3f_2246_; lean_object* v_powIdentityInst_x3f_2247_; lean_object* v_denoteEntries_2248_; lean_object* v_nextId_2249_; lean_object* v_steps_2250_; lean_object* v_queue_2251_; lean_object* v_basis_2252_; lean_object* v_diseqs_2253_; uint8_t v_recheck_2254_; lean_object* v_invSet_2255_; lean_object* v_powIdentityVarCount_2256_; lean_object* v_numEq0_x3f_2257_; uint8_t v_numEq0Updated_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2290_; 
v_toRing_2240_ = lean_ctor_get(v_s_2239_, 0);
v_invFn_x3f_2241_ = lean_ctor_get(v_s_2239_, 1);
v_semiringId_x3f_2242_ = lean_ctor_get(v_s_2239_, 2);
v_commSemiringInst_2243_ = lean_ctor_get(v_s_2239_, 3);
v_commRingInst_2244_ = lean_ctor_get(v_s_2239_, 4);
v_noZeroDivInst_x3f_2245_ = lean_ctor_get(v_s_2239_, 5);
v_fieldInst_x3f_2246_ = lean_ctor_get(v_s_2239_, 6);
v_powIdentityInst_x3f_2247_ = lean_ctor_get(v_s_2239_, 7);
v_denoteEntries_2248_ = lean_ctor_get(v_s_2239_, 8);
v_nextId_2249_ = lean_ctor_get(v_s_2239_, 9);
v_steps_2250_ = lean_ctor_get(v_s_2239_, 10);
v_queue_2251_ = lean_ctor_get(v_s_2239_, 11);
v_basis_2252_ = lean_ctor_get(v_s_2239_, 12);
v_diseqs_2253_ = lean_ctor_get(v_s_2239_, 13);
v_recheck_2254_ = lean_ctor_get_uint8(v_s_2239_, sizeof(void*)*17);
v_invSet_2255_ = lean_ctor_get(v_s_2239_, 14);
v_powIdentityVarCount_2256_ = lean_ctor_get(v_s_2239_, 15);
v_numEq0_x3f_2257_ = lean_ctor_get(v_s_2239_, 16);
v_numEq0Updated_2258_ = lean_ctor_get_uint8(v_s_2239_, sizeof(void*)*17 + 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_s_2239_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2260_ = v_s_2239_;
v_isShared_2261_ = v_isSharedCheck_2290_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_numEq0_x3f_2257_);
lean_inc(v_powIdentityVarCount_2256_);
lean_inc(v_invSet_2255_);
lean_inc(v_diseqs_2253_);
lean_inc(v_basis_2252_);
lean_inc(v_queue_2251_);
lean_inc(v_steps_2250_);
lean_inc(v_nextId_2249_);
lean_inc(v_denoteEntries_2248_);
lean_inc(v_powIdentityInst_x3f_2247_);
lean_inc(v_fieldInst_x3f_2246_);
lean_inc(v_noZeroDivInst_x3f_2245_);
lean_inc(v_commRingInst_2244_);
lean_inc(v_commSemiringInst_2243_);
lean_inc(v_semiringId_x3f_2242_);
lean_inc(v_invFn_x3f_2241_);
lean_inc(v_toRing_2240_);
lean_dec(v_s_2239_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2290_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v_id_2262_; lean_object* v_type_2263_; lean_object* v_u_2264_; lean_object* v_ringInst_2265_; lean_object* v_semiringInst_2266_; lean_object* v_charInst_x3f_2267_; lean_object* v_mulFn_x3f_2268_; lean_object* v_subFn_x3f_2269_; lean_object* v_negFn_x3f_2270_; lean_object* v_powFn_x3f_2271_; lean_object* v_intCastFn_x3f_2272_; lean_object* v_natCastFn_x3f_2273_; lean_object* v_one_x3f_2274_; lean_object* v_vars_2275_; lean_object* v_varMap_2276_; lean_object* v_denote_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2288_; 
v_id_2262_ = lean_ctor_get(v_toRing_2240_, 0);
v_type_2263_ = lean_ctor_get(v_toRing_2240_, 1);
v_u_2264_ = lean_ctor_get(v_toRing_2240_, 2);
v_ringInst_2265_ = lean_ctor_get(v_toRing_2240_, 3);
v_semiringInst_2266_ = lean_ctor_get(v_toRing_2240_, 4);
v_charInst_x3f_2267_ = lean_ctor_get(v_toRing_2240_, 5);
v_mulFn_x3f_2268_ = lean_ctor_get(v_toRing_2240_, 7);
v_subFn_x3f_2269_ = lean_ctor_get(v_toRing_2240_, 8);
v_negFn_x3f_2270_ = lean_ctor_get(v_toRing_2240_, 9);
v_powFn_x3f_2271_ = lean_ctor_get(v_toRing_2240_, 10);
v_intCastFn_x3f_2272_ = lean_ctor_get(v_toRing_2240_, 11);
v_natCastFn_x3f_2273_ = lean_ctor_get(v_toRing_2240_, 12);
v_one_x3f_2274_ = lean_ctor_get(v_toRing_2240_, 13);
v_vars_2275_ = lean_ctor_get(v_toRing_2240_, 14);
v_varMap_2276_ = lean_ctor_get(v_toRing_2240_, 15);
v_denote_2277_ = lean_ctor_get(v_toRing_2240_, 16);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_toRing_2240_);
if (v_isSharedCheck_2288_ == 0)
{
lean_object* v_unused_2289_; 
v_unused_2289_ = lean_ctor_get(v_toRing_2240_, 6);
lean_dec(v_unused_2289_);
v___x_2279_ = v_toRing_2240_;
v_isShared_2280_ = v_isSharedCheck_2288_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_denote_2277_);
lean_inc(v_varMap_2276_);
lean_inc(v_vars_2275_);
lean_inc(v_one_x3f_2274_);
lean_inc(v_natCastFn_x3f_2273_);
lean_inc(v_intCastFn_x3f_2272_);
lean_inc(v_powFn_x3f_2271_);
lean_inc(v_negFn_x3f_2270_);
lean_inc(v_subFn_x3f_2269_);
lean_inc(v_mulFn_x3f_2268_);
lean_inc(v_charInst_x3f_2267_);
lean_inc(v_semiringInst_2266_);
lean_inc(v_ringInst_2265_);
lean_inc(v_u_2264_);
lean_inc(v_type_2263_);
lean_inc(v_id_2262_);
lean_dec(v_toRing_2240_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2288_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2281_, 0, v_a_2238_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 6, v___x_2281_);
v___x_2283_ = v___x_2279_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_id_2262_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_type_2263_);
lean_ctor_set(v_reuseFailAlloc_2287_, 2, v_u_2264_);
lean_ctor_set(v_reuseFailAlloc_2287_, 3, v_ringInst_2265_);
lean_ctor_set(v_reuseFailAlloc_2287_, 4, v_semiringInst_2266_);
lean_ctor_set(v_reuseFailAlloc_2287_, 5, v_charInst_x3f_2267_);
lean_ctor_set(v_reuseFailAlloc_2287_, 6, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2287_, 7, v_mulFn_x3f_2268_);
lean_ctor_set(v_reuseFailAlloc_2287_, 8, v_subFn_x3f_2269_);
lean_ctor_set(v_reuseFailAlloc_2287_, 9, v_negFn_x3f_2270_);
lean_ctor_set(v_reuseFailAlloc_2287_, 10, v_powFn_x3f_2271_);
lean_ctor_set(v_reuseFailAlloc_2287_, 11, v_intCastFn_x3f_2272_);
lean_ctor_set(v_reuseFailAlloc_2287_, 12, v_natCastFn_x3f_2273_);
lean_ctor_set(v_reuseFailAlloc_2287_, 13, v_one_x3f_2274_);
lean_ctor_set(v_reuseFailAlloc_2287_, 14, v_vars_2275_);
lean_ctor_set(v_reuseFailAlloc_2287_, 15, v_varMap_2276_);
lean_ctor_set(v_reuseFailAlloc_2287_, 16, v_denote_2277_);
v___x_2283_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2285_; 
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2283_);
v___x_2285_ = v___x_2260_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_invFn_x3f_2241_);
lean_ctor_set(v_reuseFailAlloc_2286_, 2, v_semiringId_x3f_2242_);
lean_ctor_set(v_reuseFailAlloc_2286_, 3, v_commSemiringInst_2243_);
lean_ctor_set(v_reuseFailAlloc_2286_, 4, v_commRingInst_2244_);
lean_ctor_set(v_reuseFailAlloc_2286_, 5, v_noZeroDivInst_x3f_2245_);
lean_ctor_set(v_reuseFailAlloc_2286_, 6, v_fieldInst_x3f_2246_);
lean_ctor_set(v_reuseFailAlloc_2286_, 7, v_powIdentityInst_x3f_2247_);
lean_ctor_set(v_reuseFailAlloc_2286_, 8, v_denoteEntries_2248_);
lean_ctor_set(v_reuseFailAlloc_2286_, 9, v_nextId_2249_);
lean_ctor_set(v_reuseFailAlloc_2286_, 10, v_steps_2250_);
lean_ctor_set(v_reuseFailAlloc_2286_, 11, v_queue_2251_);
lean_ctor_set(v_reuseFailAlloc_2286_, 12, v_basis_2252_);
lean_ctor_set(v_reuseFailAlloc_2286_, 13, v_diseqs_2253_);
lean_ctor_set(v_reuseFailAlloc_2286_, 14, v_invSet_2255_);
lean_ctor_set(v_reuseFailAlloc_2286_, 15, v_powIdentityVarCount_2256_);
lean_ctor_set(v_reuseFailAlloc_2286_, 16, v_numEq0_x3f_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*17, v_recheck_2254_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*17 + 1, v_numEq0Updated_2258_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2347_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2347_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2347_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_toRing_2308_; lean_object* v_addFn_x3f_2309_; 
v_toRing_2308_ = lean_ctor_get(v_a_2304_, 0);
lean_inc_ref(v_toRing_2308_);
lean_dec(v_a_2304_);
v_addFn_x3f_2309_ = lean_ctor_get(v_toRing_2308_, 6);
if (lean_obj_tag(v_addFn_x3f_2309_) == 1)
{
lean_object* v_val_2310_; lean_object* v___x_2312_; 
lean_inc_ref(v_addFn_x3f_2309_);
lean_dec_ref(v_toRing_2308_);
v_val_2310_ = lean_ctor_get(v_addFn_x3f_2309_, 0);
lean_inc(v_val_2310_);
lean_dec_ref_known(v_addFn_x3f_2309_, 1);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v_val_2310_);
v___x_2312_ = v___x_2306_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_val_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
else
{
lean_object* v_type_2314_; lean_object* v_u_2315_; lean_object* v_semiringInst_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_expectedInst_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_del_object(v___x_2306_);
v_type_2314_ = lean_ctor_get(v_toRing_2308_, 1);
lean_inc_ref_n(v_type_2314_, 3);
v_u_2315_ = lean_ctor_get(v_toRing_2308_, 2);
lean_inc_n(v_u_2315_, 2);
v_semiringInst_2316_ = lean_ctor_get(v_toRing_2308_, 4);
lean_inc_ref(v_semiringInst_2316_);
lean_dec_ref(v_toRing_2308_);
v___x_2317_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1));
v___x_2318_ = lean_box(0);
v___x_2319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2319_, 0, v_u_2315_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
lean_inc_ref(v___x_2319_);
v___x_2320_ = l_Lean_mkConst(v___x_2317_, v___x_2319_);
v___x_2321_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4));
v___x_2322_ = l_Lean_mkConst(v___x_2321_, v___x_2319_);
v___x_2323_ = l_Lean_mkAppB(v___x_2322_, v_type_2314_, v_semiringInst_2316_);
v_expectedInst_2324_ = l_Lean_mkAppB(v___x_2320_, v_type_2314_, v___x_2323_);
v___x_2325_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6));
v___x_2326_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8));
v___x_2327_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_2314_, v_u_2315_, v___x_2325_, v___x_2326_, v_expectedInst_2324_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___f_2329_; lean_object* v___x_2330_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc_n(v_a_2328_, 2);
lean_dec_ref_known(v___x_2327_, 1);
v___f_2329_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_2329_, 0, v_a_2328_);
v___x_2330_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2329_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; 
v_unused_2338_ = lean_ctor_get(v___x_2330_, 0);
lean_dec(v_unused_2338_);
v___x_2332_ = v___x_2330_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_dec(v___x_2330_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v_a_2328_);
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2328_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v_a_2328_);
v_a_2339_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2330_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2330_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
else
{
return v___x_2327_;
}
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
v_a_2348_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2303_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2303_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec(v___y_2356_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(lean_object* v_type_2369_, lean_object* v_u_2370_, lean_object* v_instDeclName_2371_, lean_object* v_declName_2372_, lean_object* v_expectedInst_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2386_ = lean_box(0);
v___x_2387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2387_, 0, v_u_2370_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
lean_inc_ref(v___x_2387_);
v___x_2388_ = l_Lean_mkConst(v_instDeclName_2371_, v___x_2387_);
lean_inc_ref(v_type_2369_);
v___x_2389_ = l_Lean_Expr_app___override(v___x_2388_, v_type_2369_);
v___x_2390_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2389_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2392_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc_n(v_a_2391_, 2);
lean_dec_ref_known(v___x_2390_, 1);
lean_inc(v_declName_2372_);
v___x_2392_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_2372_, v_a_2391_, v_expectedInst_2373_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
lean_dec_ref_known(v___x_2392_, 1);
v___x_2393_ = l_Lean_mkConst(v_declName_2372_, v___x_2387_);
v___x_2394_ = l_Lean_mkAppB(v___x_2393_, v_type_2369_, v_a_2391_);
v___x_2395_ = l_Lean_Meta_Sym_canon(v___x_2394_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2397_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2395_, 1);
v___x_2397_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2396_, v___y_2380_);
return v___x_2397_;
}
else
{
return v___x_2395_;
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec(v_a_2391_);
lean_dec_ref_known(v___x_2387_, 2);
lean_dec(v_declName_2372_);
lean_dec_ref(v_type_2369_);
v_a_2398_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2392_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2392_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2387_, 2);
lean_dec_ref(v_expectedInst_2373_);
lean_dec(v_declName_2372_);
lean_dec_ref(v_type_2369_);
return v___x_2390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_type_2406_ = _args[0];
lean_object* v_u_2407_ = _args[1];
lean_object* v_instDeclName_2408_ = _args[2];
lean_object* v_declName_2409_ = _args[3];
lean_object* v_expectedInst_2410_ = _args[4];
lean_object* v___y_2411_ = _args[5];
lean_object* v___y_2412_ = _args[6];
lean_object* v___y_2413_ = _args[7];
lean_object* v___y_2414_ = _args[8];
lean_object* v___y_2415_ = _args[9];
lean_object* v___y_2416_ = _args[10];
lean_object* v___y_2417_ = _args[11];
lean_object* v___y_2418_ = _args[12];
lean_object* v___y_2419_ = _args[13];
lean_object* v___y_2420_ = _args[14];
lean_object* v___y_2421_ = _args[15];
lean_object* v___y_2422_ = _args[16];
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_2406_, v_u_2407_, v_instDeclName_2408_, v_declName_2409_, v_expectedInst_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec(v___y_2411_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(lean_object* v_a_2424_, lean_object* v_s_2425_){
_start:
{
lean_object* v_toRing_2426_; lean_object* v_invFn_x3f_2427_; lean_object* v_semiringId_x3f_2428_; lean_object* v_commSemiringInst_2429_; lean_object* v_commRingInst_2430_; lean_object* v_noZeroDivInst_x3f_2431_; lean_object* v_fieldInst_x3f_2432_; lean_object* v_powIdentityInst_x3f_2433_; lean_object* v_denoteEntries_2434_; lean_object* v_nextId_2435_; lean_object* v_steps_2436_; lean_object* v_queue_2437_; lean_object* v_basis_2438_; lean_object* v_diseqs_2439_; uint8_t v_recheck_2440_; lean_object* v_invSet_2441_; lean_object* v_powIdentityVarCount_2442_; lean_object* v_numEq0_x3f_2443_; uint8_t v_numEq0Updated_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2476_; 
v_toRing_2426_ = lean_ctor_get(v_s_2425_, 0);
v_invFn_x3f_2427_ = lean_ctor_get(v_s_2425_, 1);
v_semiringId_x3f_2428_ = lean_ctor_get(v_s_2425_, 2);
v_commSemiringInst_2429_ = lean_ctor_get(v_s_2425_, 3);
v_commRingInst_2430_ = lean_ctor_get(v_s_2425_, 4);
v_noZeroDivInst_x3f_2431_ = lean_ctor_get(v_s_2425_, 5);
v_fieldInst_x3f_2432_ = lean_ctor_get(v_s_2425_, 6);
v_powIdentityInst_x3f_2433_ = lean_ctor_get(v_s_2425_, 7);
v_denoteEntries_2434_ = lean_ctor_get(v_s_2425_, 8);
v_nextId_2435_ = lean_ctor_get(v_s_2425_, 9);
v_steps_2436_ = lean_ctor_get(v_s_2425_, 10);
v_queue_2437_ = lean_ctor_get(v_s_2425_, 11);
v_basis_2438_ = lean_ctor_get(v_s_2425_, 12);
v_diseqs_2439_ = lean_ctor_get(v_s_2425_, 13);
v_recheck_2440_ = lean_ctor_get_uint8(v_s_2425_, sizeof(void*)*17);
v_invSet_2441_ = lean_ctor_get(v_s_2425_, 14);
v_powIdentityVarCount_2442_ = lean_ctor_get(v_s_2425_, 15);
v_numEq0_x3f_2443_ = lean_ctor_get(v_s_2425_, 16);
v_numEq0Updated_2444_ = lean_ctor_get_uint8(v_s_2425_, sizeof(void*)*17 + 1);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_s_2425_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2446_ = v_s_2425_;
v_isShared_2447_ = v_isSharedCheck_2476_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_numEq0_x3f_2443_);
lean_inc(v_powIdentityVarCount_2442_);
lean_inc(v_invSet_2441_);
lean_inc(v_diseqs_2439_);
lean_inc(v_basis_2438_);
lean_inc(v_queue_2437_);
lean_inc(v_steps_2436_);
lean_inc(v_nextId_2435_);
lean_inc(v_denoteEntries_2434_);
lean_inc(v_powIdentityInst_x3f_2433_);
lean_inc(v_fieldInst_x3f_2432_);
lean_inc(v_noZeroDivInst_x3f_2431_);
lean_inc(v_commRingInst_2430_);
lean_inc(v_commSemiringInst_2429_);
lean_inc(v_semiringId_x3f_2428_);
lean_inc(v_invFn_x3f_2427_);
lean_inc(v_toRing_2426_);
lean_dec(v_s_2425_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2476_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v_id_2448_; lean_object* v_type_2449_; lean_object* v_u_2450_; lean_object* v_ringInst_2451_; lean_object* v_semiringInst_2452_; lean_object* v_charInst_x3f_2453_; lean_object* v_addFn_x3f_2454_; lean_object* v_mulFn_x3f_2455_; lean_object* v_subFn_x3f_2456_; lean_object* v_powFn_x3f_2457_; lean_object* v_intCastFn_x3f_2458_; lean_object* v_natCastFn_x3f_2459_; lean_object* v_one_x3f_2460_; lean_object* v_vars_2461_; lean_object* v_varMap_2462_; lean_object* v_denote_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2474_; 
v_id_2448_ = lean_ctor_get(v_toRing_2426_, 0);
v_type_2449_ = lean_ctor_get(v_toRing_2426_, 1);
v_u_2450_ = lean_ctor_get(v_toRing_2426_, 2);
v_ringInst_2451_ = lean_ctor_get(v_toRing_2426_, 3);
v_semiringInst_2452_ = lean_ctor_get(v_toRing_2426_, 4);
v_charInst_x3f_2453_ = lean_ctor_get(v_toRing_2426_, 5);
v_addFn_x3f_2454_ = lean_ctor_get(v_toRing_2426_, 6);
v_mulFn_x3f_2455_ = lean_ctor_get(v_toRing_2426_, 7);
v_subFn_x3f_2456_ = lean_ctor_get(v_toRing_2426_, 8);
v_powFn_x3f_2457_ = lean_ctor_get(v_toRing_2426_, 10);
v_intCastFn_x3f_2458_ = lean_ctor_get(v_toRing_2426_, 11);
v_natCastFn_x3f_2459_ = lean_ctor_get(v_toRing_2426_, 12);
v_one_x3f_2460_ = lean_ctor_get(v_toRing_2426_, 13);
v_vars_2461_ = lean_ctor_get(v_toRing_2426_, 14);
v_varMap_2462_ = lean_ctor_get(v_toRing_2426_, 15);
v_denote_2463_ = lean_ctor_get(v_toRing_2426_, 16);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_toRing_2426_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v_toRing_2426_, 9);
lean_dec(v_unused_2475_);
v___x_2465_ = v_toRing_2426_;
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
lean_dec(v_toRing_2426_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2474_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2467_, 0, v_a_2424_);
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
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_invFn_x3f_2427_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v_semiringId_x3f_2428_);
lean_ctor_set(v_reuseFailAlloc_2472_, 3, v_commSemiringInst_2429_);
lean_ctor_set(v_reuseFailAlloc_2472_, 4, v_commRingInst_2430_);
lean_ctor_set(v_reuseFailAlloc_2472_, 5, v_noZeroDivInst_x3f_2431_);
lean_ctor_set(v_reuseFailAlloc_2472_, 6, v_fieldInst_x3f_2432_);
lean_ctor_set(v_reuseFailAlloc_2472_, 7, v_powIdentityInst_x3f_2433_);
lean_ctor_set(v_reuseFailAlloc_2472_, 8, v_denoteEntries_2434_);
lean_ctor_set(v_reuseFailAlloc_2472_, 9, v_nextId_2435_);
lean_ctor_set(v_reuseFailAlloc_2472_, 10, v_steps_2436_);
lean_ctor_set(v_reuseFailAlloc_2472_, 11, v_queue_2437_);
lean_ctor_set(v_reuseFailAlloc_2472_, 12, v_basis_2438_);
lean_ctor_set(v_reuseFailAlloc_2472_, 13, v_diseqs_2439_);
lean_ctor_set(v_reuseFailAlloc_2472_, 14, v_invSet_2441_);
lean_ctor_set(v_reuseFailAlloc_2472_, 15, v_powIdentityVarCount_2442_);
lean_ctor_set(v_reuseFailAlloc_2472_, 16, v_numEq0_x3f_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2472_, sizeof(void*)*17, v_recheck_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2472_, sizeof(void*)*17 + 1, v_numEq0Updated_2444_);
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
lean_dec_ref_known(v_negFn_x3f_2508_, 1);
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
lean_dec_ref_known(v___x_2523_, 1);
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
lean_dec_ref_known(v___x_2592_, 1);
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
lean_dec_ref_known(v_a_2607_, 1);
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
lean_dec_ref_known(v___x_2602_, 2);
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
lean_object* v_toRing_2679_; lean_object* v_invFn_x3f_2680_; lean_object* v_semiringId_x3f_2681_; lean_object* v_commSemiringInst_2682_; lean_object* v_commRingInst_2683_; lean_object* v_noZeroDivInst_x3f_2684_; lean_object* v_fieldInst_x3f_2685_; lean_object* v_powIdentityInst_x3f_2686_; lean_object* v_denoteEntries_2687_; lean_object* v_nextId_2688_; lean_object* v_steps_2689_; lean_object* v_queue_2690_; lean_object* v_basis_2691_; lean_object* v_diseqs_2692_; uint8_t v_recheck_2693_; lean_object* v_invSet_2694_; lean_object* v_powIdentityVarCount_2695_; lean_object* v_numEq0_x3f_2696_; uint8_t v_numEq0Updated_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2729_; 
v_toRing_2679_ = lean_ctor_get(v_s_2678_, 0);
v_invFn_x3f_2680_ = lean_ctor_get(v_s_2678_, 1);
v_semiringId_x3f_2681_ = lean_ctor_get(v_s_2678_, 2);
v_commSemiringInst_2682_ = lean_ctor_get(v_s_2678_, 3);
v_commRingInst_2683_ = lean_ctor_get(v_s_2678_, 4);
v_noZeroDivInst_x3f_2684_ = lean_ctor_get(v_s_2678_, 5);
v_fieldInst_x3f_2685_ = lean_ctor_get(v_s_2678_, 6);
v_powIdentityInst_x3f_2686_ = lean_ctor_get(v_s_2678_, 7);
v_denoteEntries_2687_ = lean_ctor_get(v_s_2678_, 8);
v_nextId_2688_ = lean_ctor_get(v_s_2678_, 9);
v_steps_2689_ = lean_ctor_get(v_s_2678_, 10);
v_queue_2690_ = lean_ctor_get(v_s_2678_, 11);
v_basis_2691_ = lean_ctor_get(v_s_2678_, 12);
v_diseqs_2692_ = lean_ctor_get(v_s_2678_, 13);
v_recheck_2693_ = lean_ctor_get_uint8(v_s_2678_, sizeof(void*)*17);
v_invSet_2694_ = lean_ctor_get(v_s_2678_, 14);
v_powIdentityVarCount_2695_ = lean_ctor_get(v_s_2678_, 15);
v_numEq0_x3f_2696_ = lean_ctor_get(v_s_2678_, 16);
v_numEq0Updated_2697_ = lean_ctor_get_uint8(v_s_2678_, sizeof(void*)*17 + 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_s_2678_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2699_ = v_s_2678_;
v_isShared_2700_ = v_isSharedCheck_2729_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_numEq0_x3f_2696_);
lean_inc(v_powIdentityVarCount_2695_);
lean_inc(v_invSet_2694_);
lean_inc(v_diseqs_2692_);
lean_inc(v_basis_2691_);
lean_inc(v_queue_2690_);
lean_inc(v_steps_2689_);
lean_inc(v_nextId_2688_);
lean_inc(v_denoteEntries_2687_);
lean_inc(v_powIdentityInst_x3f_2686_);
lean_inc(v_fieldInst_x3f_2685_);
lean_inc(v_noZeroDivInst_x3f_2684_);
lean_inc(v_commRingInst_2683_);
lean_inc(v_commSemiringInst_2682_);
lean_inc(v_semiringId_x3f_2681_);
lean_inc(v_invFn_x3f_2680_);
lean_inc(v_toRing_2679_);
lean_dec(v_s_2678_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2729_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v_id_2701_; lean_object* v_type_2702_; lean_object* v_u_2703_; lean_object* v_ringInst_2704_; lean_object* v_semiringInst_2705_; lean_object* v_charInst_x3f_2706_; lean_object* v_addFn_x3f_2707_; lean_object* v_mulFn_x3f_2708_; lean_object* v_subFn_x3f_2709_; lean_object* v_negFn_x3f_2710_; lean_object* v_intCastFn_x3f_2711_; lean_object* v_natCastFn_x3f_2712_; lean_object* v_one_x3f_2713_; lean_object* v_vars_2714_; lean_object* v_varMap_2715_; lean_object* v_denote_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2727_; 
v_id_2701_ = lean_ctor_get(v_toRing_2679_, 0);
v_type_2702_ = lean_ctor_get(v_toRing_2679_, 1);
v_u_2703_ = lean_ctor_get(v_toRing_2679_, 2);
v_ringInst_2704_ = lean_ctor_get(v_toRing_2679_, 3);
v_semiringInst_2705_ = lean_ctor_get(v_toRing_2679_, 4);
v_charInst_x3f_2706_ = lean_ctor_get(v_toRing_2679_, 5);
v_addFn_x3f_2707_ = lean_ctor_get(v_toRing_2679_, 6);
v_mulFn_x3f_2708_ = lean_ctor_get(v_toRing_2679_, 7);
v_subFn_x3f_2709_ = lean_ctor_get(v_toRing_2679_, 8);
v_negFn_x3f_2710_ = lean_ctor_get(v_toRing_2679_, 9);
v_intCastFn_x3f_2711_ = lean_ctor_get(v_toRing_2679_, 11);
v_natCastFn_x3f_2712_ = lean_ctor_get(v_toRing_2679_, 12);
v_one_x3f_2713_ = lean_ctor_get(v_toRing_2679_, 13);
v_vars_2714_ = lean_ctor_get(v_toRing_2679_, 14);
v_varMap_2715_ = lean_ctor_get(v_toRing_2679_, 15);
v_denote_2716_ = lean_ctor_get(v_toRing_2679_, 16);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_toRing_2679_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; 
v_unused_2728_ = lean_ctor_get(v_toRing_2679_, 10);
lean_dec(v_unused_2728_);
v___x_2718_ = v_toRing_2679_;
v_isShared_2719_ = v_isSharedCheck_2727_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_denote_2716_);
lean_inc(v_varMap_2715_);
lean_inc(v_vars_2714_);
lean_inc(v_one_x3f_2713_);
lean_inc(v_natCastFn_x3f_2712_);
lean_inc(v_intCastFn_x3f_2711_);
lean_inc(v_negFn_x3f_2710_);
lean_inc(v_subFn_x3f_2709_);
lean_inc(v_mulFn_x3f_2708_);
lean_inc(v_addFn_x3f_2707_);
lean_inc(v_charInst_x3f_2706_);
lean_inc(v_semiringInst_2705_);
lean_inc(v_ringInst_2704_);
lean_inc(v_u_2703_);
lean_inc(v_type_2702_);
lean_inc(v_id_2701_);
lean_dec(v_toRing_2679_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2727_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_a_2677_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 10, v___x_2720_);
v___x_2722_ = v___x_2718_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_id_2701_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_type_2702_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_u_2703_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v_ringInst_2704_);
lean_ctor_set(v_reuseFailAlloc_2726_, 4, v_semiringInst_2705_);
lean_ctor_set(v_reuseFailAlloc_2726_, 5, v_charInst_x3f_2706_);
lean_ctor_set(v_reuseFailAlloc_2726_, 6, v_addFn_x3f_2707_);
lean_ctor_set(v_reuseFailAlloc_2726_, 7, v_mulFn_x3f_2708_);
lean_ctor_set(v_reuseFailAlloc_2726_, 8, v_subFn_x3f_2709_);
lean_ctor_set(v_reuseFailAlloc_2726_, 9, v_negFn_x3f_2710_);
lean_ctor_set(v_reuseFailAlloc_2726_, 10, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2726_, 11, v_intCastFn_x3f_2711_);
lean_ctor_set(v_reuseFailAlloc_2726_, 12, v_natCastFn_x3f_2712_);
lean_ctor_set(v_reuseFailAlloc_2726_, 13, v_one_x3f_2713_);
lean_ctor_set(v_reuseFailAlloc_2726_, 14, v_vars_2714_);
lean_ctor_set(v_reuseFailAlloc_2726_, 15, v_varMap_2715_);
lean_ctor_set(v_reuseFailAlloc_2726_, 16, v_denote_2716_);
v___x_2722_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2724_; 
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2722_);
v___x_2724_ = v___x_2699_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_invFn_x3f_2680_);
lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_semiringId_x3f_2681_);
lean_ctor_set(v_reuseFailAlloc_2725_, 3, v_commSemiringInst_2682_);
lean_ctor_set(v_reuseFailAlloc_2725_, 4, v_commRingInst_2683_);
lean_ctor_set(v_reuseFailAlloc_2725_, 5, v_noZeroDivInst_x3f_2684_);
lean_ctor_set(v_reuseFailAlloc_2725_, 6, v_fieldInst_x3f_2685_);
lean_ctor_set(v_reuseFailAlloc_2725_, 7, v_powIdentityInst_x3f_2686_);
lean_ctor_set(v_reuseFailAlloc_2725_, 8, v_denoteEntries_2687_);
lean_ctor_set(v_reuseFailAlloc_2725_, 9, v_nextId_2688_);
lean_ctor_set(v_reuseFailAlloc_2725_, 10, v_steps_2689_);
lean_ctor_set(v_reuseFailAlloc_2725_, 11, v_queue_2690_);
lean_ctor_set(v_reuseFailAlloc_2725_, 12, v_basis_2691_);
lean_ctor_set(v_reuseFailAlloc_2725_, 13, v_diseqs_2692_);
lean_ctor_set(v_reuseFailAlloc_2725_, 14, v_invSet_2694_);
lean_ctor_set(v_reuseFailAlloc_2725_, 15, v_powIdentityVarCount_2695_);
lean_ctor_set(v_reuseFailAlloc_2725_, 16, v_numEq0_x3f_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, sizeof(void*)*17, v_recheck_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, sizeof(void*)*17 + 1, v_numEq0Updated_2697_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = lean_unsigned_to_nat(0u);
v___x_2734_ = l_Lean_Level_ofNat(v___x_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(lean_object* v_u_2745_, lean_object* v_type_2746_, lean_object* v_semiringInst_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2760_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1));
v___x_2761_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2);
v___x_2762_ = lean_box(0);
lean_inc(v_u_2745_);
v___x_2763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2763_, 0, v_u_2745_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
lean_inc_ref(v___x_2763_);
v___x_2764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2761_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2765_, 0, v_u_2745_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
lean_inc_ref(v___x_2765_);
v___x_2766_ = l_Lean_mkConst(v___x_2760_, v___x_2765_);
v___x_2767_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_2746_, 2);
v___x_2768_ = l_Lean_mkApp3(v___x_2766_, v_type_2746_, v___x_2767_, v_type_2746_);
v___x_2769_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_2768_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v_inst_x27_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc_n(v_a_2770_, 2);
lean_dec_ref_known(v___x_2769_, 1);
v___x_2771_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4));
v___x_2772_ = l_Lean_mkConst(v___x_2771_, v___x_2763_);
lean_inc_ref(v_type_2746_);
v_inst_x27_2773_ = l_Lean_mkAppB(v___x_2772_, v_type_2746_, v_semiringInst_2747_);
v___x_2774_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6));
v___x_2775_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_2774_, v_a_2770_, v_inst_x27_2773_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
lean_dec_ref_known(v___x_2775_, 1);
v___x_2776_ = l_Lean_mkConst(v___x_2774_, v___x_2765_);
lean_inc_ref(v_type_2746_);
v___x_2777_ = l_Lean_mkApp4(v___x_2776_, v_type_2746_, v___x_2767_, v_type_2746_, v_a_2770_);
v___x_2778_ = l_Lean_Meta_Sym_canon(v___x_2777_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2780_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2779_, v___y_2754_);
return v___x_2780_;
}
else
{
return v___x_2778_;
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_a_2770_);
lean_dec_ref_known(v___x_2765_, 2);
lean_dec_ref(v_type_2746_);
v_a_2781_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2775_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2775_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_2765_, 2);
lean_dec_ref_known(v___x_2763_, 2);
lean_dec_ref(v_semiringInst_2747_);
lean_dec_ref(v_type_2746_);
return v___x_2769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___boxed(lean_object* v_u_2789_, lean_object* v_type_2790_, lean_object* v_semiringInst_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2789_, v_type_2790_, v_semiringInst_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec(v___y_2792_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2851_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2851_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2851_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v_toRing_2822_; lean_object* v_powFn_x3f_2823_; 
v_toRing_2822_ = lean_ctor_get(v_a_2818_, 0);
lean_inc_ref(v_toRing_2822_);
lean_dec(v_a_2818_);
v_powFn_x3f_2823_ = lean_ctor_get(v_toRing_2822_, 10);
if (lean_obj_tag(v_powFn_x3f_2823_) == 1)
{
lean_object* v_val_2824_; lean_object* v___x_2826_; 
lean_inc_ref(v_powFn_x3f_2823_);
lean_dec_ref(v_toRing_2822_);
v_val_2824_ = lean_ctor_get(v_powFn_x3f_2823_, 0);
lean_inc(v_val_2824_);
lean_dec_ref_known(v_powFn_x3f_2823_, 1);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v_val_2824_);
v___x_2826_ = v___x_2820_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_val_2824_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
else
{
lean_object* v_type_2828_; lean_object* v_u_2829_; lean_object* v_semiringInst_2830_; lean_object* v___x_2831_; 
lean_del_object(v___x_2820_);
v_type_2828_ = lean_ctor_get(v_toRing_2822_, 1);
lean_inc_ref(v_type_2828_);
v_u_2829_ = lean_ctor_get(v_toRing_2822_, 2);
lean_inc(v_u_2829_);
v_semiringInst_2830_ = lean_ctor_get(v_toRing_2822_, 4);
lean_inc_ref(v_semiringInst_2830_);
lean_dec_ref(v_toRing_2822_);
v___x_2831_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_2829_, v_type_2828_, v_semiringInst_2830_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___f_2833_; lean_object* v___x_2834_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc_n(v_a_2832_, 2);
lean_dec_ref_known(v___x_2831_, 1);
v___f_2833_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_2833_, 0, v_a_2832_);
v___x_2834_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(v___f_2833_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; 
v_unused_2842_ = lean_ctor_get(v___x_2834_, 0);
lean_dec(v_unused_2842_);
v___x_2836_ = v___x_2834_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_dec(v___x_2834_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v_a_2832_);
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2832_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v_a_2832_);
v_a_2843_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2834_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2834_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
else
{
return v___x_2831_;
}
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
v_a_2852_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2817_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2817_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec(v___y_2860_);
return v_res_2872_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2));
v___x_2877_ = lean_unsigned_to_nat(39u);
v___x_2878_ = lean_unsigned_to_nat(159u);
v___x_2879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1));
v___x_2880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0));
v___x_2881_ = l_mkPanicMessageWithDecl(v___x_2880_, v___x_2879_, v___x_2878_, v___x_2877_, v___x_2876_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
switch(lean_obj_tag(v_a_2882_))
{
case 0:
{
lean_object* v_k_2895_; lean_object* v___x_2896_; 
v_k_2895_ = lean_ctor_get(v_a_2882_, 0);
lean_inc(v_k_2895_);
lean_dec_ref_known(v_a_2882_, 1);
v___x_2896_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_2895_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
lean_dec(v_k_2895_);
return v___x_2896_;
}
case 1:
{
lean_object* v_k_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v_k_2897_ = lean_ctor_get(v_a_2882_, 0);
lean_inc(v_k_2897_);
lean_dec_ref_known(v_a_2882_, 1);
v___x_2898_ = lean_nat_to_int(v_k_2897_);
v___x_2899_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v___x_2898_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
lean_dec(v___x_2898_);
return v___x_2899_;
}
case 3:
{
lean_object* v_i_2900_; lean_object* v___x_2901_; 
v_i_2900_ = lean_ctor_get(v_a_2882_, 0);
lean_inc(v_i_2900_);
lean_dec_ref_known(v_a_2882_, 1);
v___x_2901_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2903_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
v___x_2903_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2921_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2921_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2921_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___y_2909_; lean_object* v_toSemiring_2914_; lean_object* v_vars_2915_; lean_object* v_size_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; 
v_toSemiring_2914_ = lean_ctor_get(v_a_2904_, 0);
lean_inc_ref(v_toSemiring_2914_);
lean_dec(v_a_2904_);
v_vars_2915_ = lean_ctor_get(v_toSemiring_2914_, 9);
lean_inc_ref(v_vars_2915_);
lean_dec_ref(v_toSemiring_2914_);
v_size_2916_ = lean_ctor_get(v_vars_2915_, 2);
v___x_2917_ = l_Lean_instInhabitedExpr;
v___x_2918_ = lean_nat_dec_lt(v_i_2900_, v_size_2916_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; 
lean_dec_ref(v_vars_2915_);
lean_dec(v_i_2900_);
v___x_2919_ = l_outOfBounds___redArg(v___x_2917_);
v___y_2909_ = v___x_2919_;
goto v___jp_2908_;
}
else
{
lean_object* v___x_2920_; 
v___x_2920_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2917_, v_vars_2915_, v_i_2900_);
lean_dec(v_i_2900_);
lean_dec_ref(v_vars_2915_);
v___y_2909_ = v___x_2920_;
goto v___jp_2908_;
}
v___jp_2908_:
{
lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2910_ = l_Lean_Expr_app___override(v_a_2902_, v___y_2909_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2910_);
v___x_2912_ = v___x_2906_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v_a_2902_);
lean_dec(v_i_2900_);
v_a_2922_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2903_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2903_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_dec(v_i_2900_);
return v___x_2901_;
}
}
case 5:
{
lean_object* v_a_2930_; lean_object* v_b_2931_; lean_object* v___x_2932_; 
v_a_2930_ = lean_ctor_get(v_a_2882_, 0);
lean_inc_ref(v_a_2930_);
v_b_2931_ = lean_ctor_get(v_a_2882_, 1);
lean_inc_ref(v_b_2931_);
lean_dec_ref_known(v_a_2882_, 2);
v___x_2932_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2934_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref_known(v___x_2932_, 1);
v___x_2934_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2930_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2936_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___x_2934_, 1);
v___x_2936_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2931_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2945_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2945_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2945_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2941_; lean_object* v___x_2943_; 
v___x_2941_ = l_Lean_mkAppB(v_a_2933_, v_a_2935_, v_a_2937_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2941_);
v___x_2943_ = v___x_2939_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
else
{
lean_dec(v_a_2935_);
lean_dec(v_a_2933_);
return v___x_2936_;
}
}
else
{
lean_dec(v_a_2933_);
lean_dec_ref(v_b_2931_);
return v___x_2934_;
}
}
else
{
lean_dec_ref(v_b_2931_);
lean_dec_ref(v_a_2930_);
return v___x_2932_;
}
}
case 7:
{
lean_object* v_a_2946_; lean_object* v_b_2947_; lean_object* v___x_2948_; 
v_a_2946_ = lean_ctor_get(v_a_2882_, 0);
lean_inc_ref(v_a_2946_);
v_b_2947_ = lean_ctor_get(v_a_2882_, 1);
lean_inc_ref(v_b_2947_);
lean_dec_ref_known(v_a_2882_, 2);
v___x_2948_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2950_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2950_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2946_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2952_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2950_, 1);
v___x_2952_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_2947_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2961_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_2961_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2961_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2957_ = l_Lean_mkAppB(v_a_2949_, v_a_2951_, v_a_2953_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2957_);
v___x_2959_ = v___x_2955_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___x_2957_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
else
{
lean_dec(v_a_2951_);
lean_dec(v_a_2949_);
return v___x_2952_;
}
}
else
{
lean_dec(v_a_2949_);
lean_dec_ref(v_b_2947_);
return v___x_2950_;
}
}
else
{
lean_dec_ref(v_b_2947_);
lean_dec_ref(v_a_2946_);
return v___x_2948_;
}
}
case 8:
{
lean_object* v_a_2962_; lean_object* v_k_2963_; lean_object* v___x_2964_; 
v_a_2962_ = lean_ctor_get(v_a_2882_, 0);
lean_inc_ref(v_a_2962_);
v_k_2963_ = lean_ctor_get(v_a_2882_, 1);
lean_inc(v_k_2963_);
lean_dec_ref_known(v_a_2882_, 2);
v___x_2964_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2966_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
v___x_2966_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2962_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2976_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2969_ = v___x_2966_;
v_isShared_2970_ = v_isSharedCheck_2976_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2966_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2976_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2971_ = l_Lean_mkNatLit(v_k_2963_);
v___x_2972_ = l_Lean_mkAppB(v_a_2965_, v_a_2967_, v___x_2971_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2972_);
v___x_2974_ = v___x_2969_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
else
{
lean_dec(v_a_2965_);
lean_dec(v_k_2963_);
return v___x_2966_;
}
}
else
{
lean_dec(v_k_2963_);
lean_dec_ref(v_a_2962_);
return v___x_2964_;
}
}
default: 
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec_ref(v_a_2882_);
v___x_2977_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3);
v___x_2978_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___x_2977_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
return v___x_2978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec(v_a_2980_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(lean_object* v_type_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_2993_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___boxed(lean_object* v_type_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(v_type_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec(v___y_3008_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(lean_object* v_e_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_e_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3036_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v___x_3034_, 1);
v___x_3036_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3035_, v_a_3028_);
return v___x_3036_;
}
else
{
return v___x_3034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(lean_object* v_e_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(v_e_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
lean_dec(v_a_3042_);
lean_dec_ref(v_a_3041_);
lean_dec(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec(v_a_3038_);
return v_res_3050_;
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
