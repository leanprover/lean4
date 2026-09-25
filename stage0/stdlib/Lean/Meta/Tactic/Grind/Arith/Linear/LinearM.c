// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.Types public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "`grind` internal error, invalid structure id"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructLinearM_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructLinearM = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructLinearM_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "`grind linarith` internal error, structure is not a ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "`grind linarith` internal error, structure is not a commutative ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__6_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__7_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_4_, v_a_1_, v_a_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg___boxed(lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_6_, v_a_7_);
lean_dec_ref(v_a_7_);
lean_dec(v_a_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27(lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_10_, v_a_18_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___boxed(lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Meta_Grind_Arith_Linear_get_x27(v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_);
lean_dec(v_a_31_);
lean_dec_ref(v_a_30_);
lean_dec(v_a_29_);
lean_dec_ref(v_a_28_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
lean_dec(v_a_23_);
lean_dec(v_a_22_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg(lean_object* v_f_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_38_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_37_, v_f_34_, v_a_35_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg___boxed(lean_object* v_f_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg(v_f_39_, v_a_40_);
lean_dec(v_a_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27(lean_object* v_f_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_56_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_55_, v_f_43_, v_a_44_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___boxed(lean_object* v_f_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Meta_Grind_Arith_Linear_modify_x27(v_f_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
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
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift___redArg(lean_object* v_inst_70_, lean_object* v_inst_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_apply_2(v_inst_70_, lean_box(0), v_inst_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift(lean_object* v_m_73_, lean_object* v_n_74_, lean_object* v_inst_75_, lean_object* v_inst_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_apply_2(v_inst_75_, lean_box(0), v_inst_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg(lean_object* v_structId_78_, lean_object* v_x_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_91_; 
lean_inc(v_a_89_);
lean_inc_ref(v_a_88_);
lean_inc(v_a_87_);
lean_inc_ref(v_a_86_);
lean_inc(v_a_85_);
lean_inc_ref(v_a_84_);
lean_inc(v_a_83_);
lean_inc_ref(v_a_82_);
lean_inc(v_a_81_);
lean_inc(v_a_80_);
v___x_91_ = lean_apply_12(v_x_79_, v_structId_78_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, lean_box(0));
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg___boxed(lean_object* v_structId_92_, lean_object* v_x_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg(v_structId_92_, v_x_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec(v_a_94_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run(lean_object* v_00_u03b1_106_, lean_object* v_structId_107_, lean_object* v_x_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___x_120_; 
lean_inc(v_a_118_);
lean_inc_ref(v_a_117_);
lean_inc(v_a_116_);
lean_inc_ref(v_a_115_);
lean_inc(v_a_114_);
lean_inc_ref(v_a_113_);
lean_inc(v_a_112_);
lean_inc_ref(v_a_111_);
lean_inc(v_a_110_);
lean_inc(v_a_109_);
v___x_120_ = lean_apply_12(v_x_108_, v_structId_107_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, lean_box(0));
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___boxed(lean_object* v_00_u03b1_121_, lean_object* v_structId_122_, lean_object* v_x_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_run(v_00_u03b1_121_, v_structId_122_, v_x_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
lean_dec(v_a_124_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg(lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; 
lean_inc(v_a_136_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v_a_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg___boxed(lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg(v_a_139_);
lean_dec(v_a_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId(lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_154_; 
lean_inc(v_a_142_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v_a_142_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___boxed(lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Meta_Grind_Arith_Linear_getStructId(v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec(v_a_156_);
lean_dec(v_a_155_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(lean_object* v_msgData_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; lean_object* v_env_175_; lean_object* v___x_176_; lean_object* v_toCold_177_; lean_object* v_mctx_178_; lean_object* v_lctx_179_; lean_object* v_options_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_174_ = lean_st_ref_get(v___y_172_);
v_env_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc_ref(v_env_175_);
lean_dec(v___x_174_);
v___x_176_ = lean_st_ref_get(v___y_170_);
v_toCold_177_ = lean_ctor_get(v___y_171_, 0);
v_mctx_178_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref(v_mctx_178_);
lean_dec(v___x_176_);
v_lctx_179_ = lean_ctor_get(v___y_169_, 2);
v_options_180_ = lean_ctor_get(v_toCold_177_, 2);
lean_inc_ref(v_options_180_);
lean_inc_ref(v_lctx_179_);
v___x_181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_181_, 0, v_env_175_);
lean_ctor_set(v___x_181_, 1, v_mctx_178_);
lean_ctor_set(v___x_181_, 2, v_lctx_179_);
lean_ctor_set(v___x_181_, 3, v_options_180_);
v___x_182_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_msgData_168_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0___boxed(lean_object* v_msgData_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msgData_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_ref_197_; lean_object* v___x_198_; lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_207_; 
v_ref_197_ = lean_ctor_get(v___y_194_, 2);
v___x_198_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_207_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
lean_inc(v_ref_197_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_ref_197_);
lean_ctor_set(v___x_203_, 1, v_a_199_);
if (v_isShared_202_ == 0)
{
lean_ctor_set_tag(v___x_201_, 1);
lean_ctor_set(v___x_201_, 0, v___x_203_);
v___x_205_ = v___x_201_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg___boxed(lean_object* v_msg_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v_msg_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_214_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_219_, v_a_227_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_244_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_244_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_244_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_244_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_structs_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v_structs_235_ = lean_ctor_get(v_a_231_, 0);
lean_inc_ref(v_structs_235_);
lean_dec(v_a_231_);
v___x_236_ = lean_array_get_size(v_structs_235_);
v___x_237_ = lean_nat_dec_lt(v_a_218_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec_ref(v_structs_235_);
lean_del_object(v___x_233_);
v___x_238_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1, &l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1);
v___x_239_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_238_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_array_fget(v_structs_235_, v_a_218_);
lean_dec_ref(v_structs_235_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_240_);
v___x_242_ = v___x_233_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
v_a_245_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_230_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_230_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___boxed(lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec(v_a_254_);
lean_dec(v_a_253_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(lean_object* v_00_u03b1_266_, lean_object* v_msg_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v_msg_267_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___boxed(lean_object* v_00_u03b1_281_, lean_object* v_msg_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(v_00_u03b1_281_, v_msg_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec(v___y_284_);
lean_dec(v___y_283_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(lean_object* v_ringId_x3f_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
if (lean_obj_tag(v_ringId_x3f_297_) == 1)
{
lean_object* v_val_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_337_; 
v_val_309_ = lean_ctor_get(v_ringId_x3f_297_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_ringId_x3f_297_);
if (v_isSharedCheck_337_ == 0)
{
v___x_311_ = v_ringId_x3f_297_;
v_isShared_312_ = v_isSharedCheck_337_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_val_309_);
lean_dec(v_ringId_x3f_297_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_337_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = 0;
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_315_, 0, v_val_309_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*2, v___x_313_);
v___x_316_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_315_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec_ref_known(v___x_315_, 2);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_328_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_328_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_328_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_328_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v_toRing_321_; lean_object* v___x_323_; 
v_toRing_321_ = lean_ctor_get(v_a_317_, 0);
lean_inc_ref(v_toRing_321_);
lean_dec(v_a_317_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v_toRing_321_);
v___x_323_ = v___x_311_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_toRing_321_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_325_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_323_);
v___x_325_ = v___x_319_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_del_object(v___x_311_);
v_a_329_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_316_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_316_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v_ringId_x3f_297_);
v___x_338_ = lean_box(0);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f___boxed(lean_object* v_ringId_x3f_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(v_ringId_x3f_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec(v_a_341_);
return v_res_352_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0));
v___x_355_ = l_Lean_stringToMessageData(v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1);
v___x_362_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_361_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___boxed(lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_363_, v_a_364_, v_a_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing(lean_object* v_00_u03b1_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_377_, v_a_378_, v_a_379_, v_a_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___boxed(lean_object* v_00_u03b1_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing(v_00_u03b1_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec(v_a_385_);
lean_dec(v_a_384_);
return v_res_396_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0));
v___x_399_ = l_Lean_stringToMessageData(v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1);
v___x_406_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_405_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___boxed(lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(lean_object* v_00_u03b1_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_421_, v_a_422_, v_a_423_, v_a_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___boxed(lean_object* v_00_u03b1_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(v_00_u03b1_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec(v_a_429_);
lean_dec(v_a_428_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v_ringId_x3f_455_; lean_object* v___x_456_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_453_, 1);
v_ringId_x3f_455_ = lean_ctor_get(v_a_454_, 1);
lean_inc(v_ringId_x3f_455_);
lean_dec(v_a_454_);
v___x_456_ = l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(v_ringId_x3f_455_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
return v___x_456_;
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_a_457_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_453_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_453_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f___boxed(lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec(v_a_466_);
lean_dec(v_a_465_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(lean_object* v_e_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_Meta_Sym_canon(v_e_478_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_493_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v___x_493_ = l_Lean_Meta_Sym_shareCommon(v_a_492_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
return v___x_493_;
}
else
{
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0___boxed(lean_object* v_e_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(v_e_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec(v___y_496_);
lean_dec(v___y_495_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(lean_object* v_e_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_508_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1___boxed(lean_object* v_e_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(v_e_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec(v___y_524_);
lean_dec(v___y_523_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_564_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_564_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_564_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_564_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
if (lean_obj_tag(v_a_555_) == 1)
{
lean_object* v_val_559_; lean_object* v___x_561_; 
v_val_559_ = lean_ctor_get(v_a_555_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v_a_555_, 1);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v_val_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_val_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
else
{
lean_object* v___x_563_; 
lean_del_object(v___x_557_);
lean_dec(v_a_555_);
v___x_563_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_549_, v_a_550_, v_a_551_, v_a_552_);
return v___x_563_;
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v_a_565_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_554_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_554_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed(lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec(v_a_574_);
lean_dec(v_a_573_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object* v_x_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v_ringId_x3f_601_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v_ringId_x3f_601_ = lean_ctor_get(v_a_600_, 1);
lean_inc(v_ringId_x3f_601_);
lean_dec(v_a_600_);
if (lean_obj_tag(v_ringId_x3f_601_) == 1)
{
lean_object* v_val_602_; uint8_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_val_602_ = lean_ctor_get(v_ringId_x3f_601_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v_ringId_x3f_601_, 1);
v___x_603_ = 0;
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_605_, 0, v_val_602_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*2, v___x_603_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
lean_inc(v_a_593_);
lean_inc_ref(v_a_592_);
lean_inc(v_a_591_);
lean_inc_ref(v_a_590_);
lean_inc(v_a_589_);
lean_inc(v_a_588_);
v___x_606_ = lean_apply_12(v_x_586_, v___x_605_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, lean_box(0));
return v___x_606_;
}
else
{
lean_object* v___x_607_; 
lean_dec(v_ringId_x3f_601_);
lean_dec_ref(v_x_586_);
v___x_607_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_594_, v_a_595_, v_a_596_, v_a_597_);
return v___x_607_;
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_x_586_);
v_a_608_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_599_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_599_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg___boxed(lean_object* v_x_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v_x_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec(v_a_618_);
lean_dec(v_a_617_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM(lean_object* v_00_u03b1_630_, lean_object* v_x_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v_x_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___boxed(lean_object* v_00_u03b1_645_, lean_object* v_x_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Meta_Grind_Arith_Linear_withRingM(v_00_u03b1_645_, v_x_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
lean_dec(v_a_648_);
lean_dec(v_a_647_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0(lean_object* v_f_660_, lean_object* v_s_661_){
_start:
{
lean_object* v_toRing_662_; lean_object* v_invFn_x3f_663_; lean_object* v_divFn_x3f_664_; lean_object* v_semiringId_x3f_665_; lean_object* v_commSemiringInst_666_; lean_object* v_commRingInst_667_; lean_object* v_noZeroDivInst_x3f_668_; lean_object* v_fieldInst_x3f_669_; lean_object* v_powIdentityInst_x3f_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
v_toRing_662_ = lean_ctor_get(v_s_661_, 0);
v_invFn_x3f_663_ = lean_ctor_get(v_s_661_, 1);
v_divFn_x3f_664_ = lean_ctor_get(v_s_661_, 2);
v_semiringId_x3f_665_ = lean_ctor_get(v_s_661_, 3);
v_commSemiringInst_666_ = lean_ctor_get(v_s_661_, 4);
v_commRingInst_667_ = lean_ctor_get(v_s_661_, 5);
v_noZeroDivInst_x3f_668_ = lean_ctor_get(v_s_661_, 6);
v_fieldInst_x3f_669_ = lean_ctor_get(v_s_661_, 7);
v_powIdentityInst_x3f_670_ = lean_ctor_get(v_s_661_, 8);
v_isSharedCheck_678_ = !lean_is_exclusive(v_s_661_);
if (v_isSharedCheck_678_ == 0)
{
v___x_672_ = v_s_661_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_powIdentityInst_x3f_670_);
lean_inc(v_fieldInst_x3f_669_);
lean_inc(v_noZeroDivInst_x3f_668_);
lean_inc(v_commRingInst_667_);
lean_inc(v_commSemiringInst_666_);
lean_inc(v_semiringId_x3f_665_);
lean_inc(v_divFn_x3f_664_);
lean_inc(v_invFn_x3f_663_);
lean_inc(v_toRing_662_);
lean_dec(v_s_661_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_apply_1(v_f_660_, v_toRing_662_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_invFn_x3f_663_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_divFn_x3f_664_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_semiringId_x3f_665_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v_commSemiringInst_666_);
lean_ctor_set(v_reuseFailAlloc_677_, 5, v_commRingInst_667_);
lean_ctor_set(v_reuseFailAlloc_677_, 6, v_noZeroDivInst_x3f_668_);
lean_ctor_set(v_reuseFailAlloc_677_, 7, v_fieldInst_x3f_669_);
lean_ctor_set(v_reuseFailAlloc_677_, 8, v_powIdentityInst_x3f_670_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(lean_object* v_f_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v___f_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___f_692_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0), 2, 1);
lean_closure_set(v___f_692_, 0, v_f_679_);
v___x_693_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed), 13, 1);
lean_closure_set(v___x_693_, 0, v___f_692_);
v___x_694_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_693_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1___boxed(lean_object* v_f_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(v_f_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec(v___y_697_);
lean_dec(v___y_696_);
return v_res_708_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1(void){
_start:
{
lean_object* v___f_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___f_710_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0));
v___x_711_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed), 12, 0);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v___f_710_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM(void){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0(lean_object* v_____do__lift_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_toRingState_727_; lean_object* v___x_728_; 
v_toRingState_727_ = lean_ctor_get(v_____do__lift_714_, 0);
lean_inc_ref(v_toRingState_727_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v_toRingState_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0___boxed(lean_object* v_____do__lift_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0(v_____do__lift_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec_ref(v_____do__lift_729_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__1(lean_object* v_f_743_, lean_object* v_s_744_){
_start:
{
lean_object* v_toRingState_745_; lean_object* v_denoteEntries_746_; lean_object* v_nextId_747_; lean_object* v_steps_748_; lean_object* v_queue_749_; lean_object* v_basis_750_; lean_object* v_diseqs_751_; uint8_t v_recheck_752_; lean_object* v_invSet_753_; lean_object* v_powIdentityVarCount_754_; lean_object* v_numEq0_x3f_755_; uint8_t v_numEq0Updated_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_764_; 
v_toRingState_745_ = lean_ctor_get(v_s_744_, 0);
v_denoteEntries_746_ = lean_ctor_get(v_s_744_, 1);
v_nextId_747_ = lean_ctor_get(v_s_744_, 2);
v_steps_748_ = lean_ctor_get(v_s_744_, 3);
v_queue_749_ = lean_ctor_get(v_s_744_, 4);
v_basis_750_ = lean_ctor_get(v_s_744_, 5);
v_diseqs_751_ = lean_ctor_get(v_s_744_, 6);
v_recheck_752_ = lean_ctor_get_uint8(v_s_744_, sizeof(void*)*10);
v_invSet_753_ = lean_ctor_get(v_s_744_, 7);
v_powIdentityVarCount_754_ = lean_ctor_get(v_s_744_, 8);
v_numEq0_x3f_755_ = lean_ctor_get(v_s_744_, 9);
v_numEq0Updated_756_ = lean_ctor_get_uint8(v_s_744_, sizeof(void*)*10 + 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_s_744_);
if (v_isSharedCheck_764_ == 0)
{
v___x_758_ = v_s_744_;
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_numEq0_x3f_755_);
lean_inc(v_powIdentityVarCount_754_);
lean_inc(v_invSet_753_);
lean_inc(v_diseqs_751_);
lean_inc(v_basis_750_);
lean_inc(v_queue_749_);
lean_inc(v_steps_748_);
lean_inc(v_nextId_747_);
lean_inc(v_denoteEntries_746_);
lean_inc(v_toRingState_745_);
lean_dec(v_s_744_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = lean_apply_1(v_f_743_, v_toRingState_745_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_760_);
v___x_762_ = v___x_758_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_denoteEntries_746_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_nextId_747_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_steps_748_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_queue_749_);
lean_ctor_set(v_reuseFailAlloc_763_, 5, v_basis_750_);
lean_ctor_set(v_reuseFailAlloc_763_, 6, v_diseqs_751_);
lean_ctor_set(v_reuseFailAlloc_763_, 7, v_invSet_753_);
lean_ctor_set(v_reuseFailAlloc_763_, 8, v_powIdentityVarCount_754_);
lean_ctor_set(v_reuseFailAlloc_763_, 9, v_numEq0_x3f_755_);
lean_ctor_set_uint8(v_reuseFailAlloc_763_, sizeof(void*)*10, v_recheck_752_);
lean_ctor_set_uint8(v_reuseFailAlloc_763_, sizeof(void*)*10 + 1, v_numEq0Updated_756_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2(lean_object* v_f_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__1), 2, 1);
lean_closure_set(v___f_778_, 0, v_f_765_);
v___x_779_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___boxed), 13, 1);
lean_closure_set(v___x_779_, 0, v___f_778_);
v___x_780_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_779_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2___boxed(lean_object* v_f_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2(v_f_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec(v___y_783_);
lean_dec(v___y_782_);
return v_res_794_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0(void){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_instMonadEIO___redArg();
return v___x_795_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0);
v___x_797_ = l_StateRefT_x27_instMonad___redArg(v___x_796_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM(void){
_start:
{
lean_object* v___x_805_; lean_object* v_toApplicative_806_; lean_object* v_toFunctor_807_; lean_object* v_toSeq_808_; lean_object* v_toSeqLeft_809_; lean_object* v_toSeqRight_810_; lean_object* v___f_811_; lean_object* v___f_812_; lean_object* v___f_813_; lean_object* v___f_814_; lean_object* v___x_815_; lean_object* v___f_816_; lean_object* v___f_817_; lean_object* v___f_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v_toApplicative_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_861_; 
v___x_805_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1);
v_toApplicative_806_ = lean_ctor_get(v___x_805_, 0);
v_toFunctor_807_ = lean_ctor_get(v_toApplicative_806_, 0);
v_toSeq_808_ = lean_ctor_get(v_toApplicative_806_, 2);
v_toSeqLeft_809_ = lean_ctor_get(v_toApplicative_806_, 3);
v_toSeqRight_810_ = lean_ctor_get(v_toApplicative_806_, 4);
v___f_811_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__2));
v___f_812_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__3));
lean_inc_ref_n(v_toFunctor_807_, 2);
v___f_813_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_813_, 0, v_toFunctor_807_);
v___f_814_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_814_, 0, v_toFunctor_807_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v___f_813_);
lean_ctor_set(v___x_815_, 1, v___f_814_);
lean_inc(v_toSeqRight_810_);
v___f_816_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_816_, 0, v_toSeqRight_810_);
lean_inc(v_toSeqLeft_809_);
v___f_817_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_817_, 0, v_toSeqLeft_809_);
lean_inc(v_toSeq_808_);
v___f_818_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_818_, 0, v_toSeq_808_);
v___x_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_819_, 0, v___x_815_);
lean_ctor_set(v___x_819_, 1, v___f_811_);
lean_ctor_set(v___x_819_, 2, v___f_818_);
lean_ctor_set(v___x_819_, 3, v___f_817_);
lean_ctor_set(v___x_819_, 4, v___f_816_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v___f_812_);
v___x_821_ = l_StateRefT_x27_instMonad___redArg(v___x_820_);
v_toApplicative_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v___x_821_, 1);
lean_dec(v_unused_862_);
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_861_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_toApplicative_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_861_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_toFunctor_826_; lean_object* v_toSeq_827_; lean_object* v_toSeqLeft_828_; lean_object* v_toSeqRight_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_859_; 
v_toFunctor_826_ = lean_ctor_get(v_toApplicative_822_, 0);
v_toSeq_827_ = lean_ctor_get(v_toApplicative_822_, 2);
v_toSeqLeft_828_ = lean_ctor_get(v_toApplicative_822_, 3);
v_toSeqRight_829_ = lean_ctor_get(v_toApplicative_822_, 4);
v_isSharedCheck_859_ = !lean_is_exclusive(v_toApplicative_822_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; 
v_unused_860_ = lean_ctor_get(v_toApplicative_822_, 1);
lean_dec(v_unused_860_);
v___x_831_ = v_toApplicative_822_;
v_isShared_832_ = v_isSharedCheck_859_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_toSeqRight_829_);
lean_inc(v_toSeqLeft_828_);
lean_inc(v_toSeq_827_);
lean_inc(v_toFunctor_826_);
lean_dec(v_toApplicative_822_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_859_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___f_833_; lean_object* v___f_834_; lean_object* v___f_835_; lean_object* v___f_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v___f_840_; lean_object* v___f_841_; lean_object* v___f_842_; lean_object* v___x_844_; 
v___f_833_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__4));
v___f_834_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__5));
v___f_835_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__6));
v___f_836_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__7));
lean_inc_ref(v_toFunctor_826_);
v___f_837_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_837_, 0, v_toFunctor_826_);
v___f_838_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_838_, 0, v_toFunctor_826_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___f_837_);
lean_ctor_set(v___x_839_, 1, v___f_838_);
v___f_840_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_840_, 0, v_toSeqRight_829_);
v___f_841_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_841_, 0, v_toSeqLeft_828_);
v___f_842_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_842_, 0, v_toSeq_827_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 4, v___f_840_);
lean_ctor_set(v___x_831_, 3, v___f_841_);
lean_ctor_set(v___x_831_, 2, v___f_842_);
lean_ctor_set(v___x_831_, 1, v___f_835_);
lean_ctor_set(v___x_831_, 0, v___x_839_);
v___x_844_ = v___x_831_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v___f_835_);
lean_ctor_set(v_reuseFailAlloc_858_, 2, v___f_842_);
lean_ctor_set(v_reuseFailAlloc_858_, 3, v___f_841_);
lean_ctor_set(v_reuseFailAlloc_858_, 4, v___f_840_);
v___x_844_ = v_reuseFailAlloc_858_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_846_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v___f_836_);
lean_ctor_set(v___x_824_, 0, v___x_844_);
v___x_846_ = v___x_824_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___f_836_);
v___x_846_ = v_reuseFailAlloc_857_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_847_ = l_StateRefT_x27_instMonad___redArg(v___x_846_);
v___x_848_ = l_ReaderT_instMonad___redArg(v___x_847_);
v___x_849_ = l_StateRefT_x27_instMonad___redArg(v___x_848_);
v___x_850_ = l_ReaderT_instMonad___redArg(v___x_849_);
v___x_851_ = l_ReaderT_instMonad___redArg(v___x_850_);
v___x_852_ = l_StateRefT_x27_instMonad___redArg(v___x_851_);
v___x_853_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__8));
v___x_854_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_854_, 0, lean_box(0));
lean_closure_set(v___x_854_, 1, lean_box(0));
lean_closure_set(v___x_854_, 2, v___x_852_);
lean_closure_set(v___x_854_, 3, lean_box(0));
lean_closure_set(v___x_854_, 4, lean_box(0));
lean_closure_set(v___x_854_, 5, v___x_853_);
lean_closure_set(v___x_854_, 6, v___f_833_);
v___x_855_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_withRingM___boxed), 14, 2);
lean_closure_set(v___x_855_, 0, lean_box(0));
lean_closure_set(v___x_855_, 1, v___x_854_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___f_834_);
return v___x_856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1(lean_object* v___f_863_, lean_object* v___x_864_, lean_object* v_x_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___x_878_; lean_object* v_toApplicative_879_; lean_object* v_toFunctor_880_; lean_object* v_toSeq_881_; lean_object* v_toSeqLeft_882_; lean_object* v_toSeqRight_883_; lean_object* v___f_884_; lean_object* v___f_885_; lean_object* v___f_886_; lean_object* v___f_887_; lean_object* v___x_888_; lean_object* v___f_889_; lean_object* v___f_890_; lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v_toApplicative_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_955_; 
v___x_878_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1);
v_toApplicative_879_ = lean_ctor_get(v___x_878_, 0);
v_toFunctor_880_ = lean_ctor_get(v_toApplicative_879_, 0);
v_toSeq_881_ = lean_ctor_get(v_toApplicative_879_, 2);
v_toSeqLeft_882_ = lean_ctor_get(v_toApplicative_879_, 3);
v_toSeqRight_883_ = lean_ctor_get(v_toApplicative_879_, 4);
v___f_884_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__2));
v___f_885_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__3));
lean_inc_ref_n(v_toFunctor_880_, 2);
v___f_886_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_886_, 0, v_toFunctor_880_);
v___f_887_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_887_, 0, v_toFunctor_880_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___f_886_);
lean_ctor_set(v___x_888_, 1, v___f_887_);
lean_inc(v_toSeqRight_883_);
v___f_889_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_889_, 0, v_toSeqRight_883_);
lean_inc(v_toSeqLeft_882_);
v___f_890_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_890_, 0, v_toSeqLeft_882_);
lean_inc(v_toSeq_881_);
v___f_891_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_891_, 0, v_toSeq_881_);
v___x_892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_892_, 0, v___x_888_);
lean_ctor_set(v___x_892_, 1, v___f_884_);
lean_ctor_set(v___x_892_, 2, v___f_891_);
lean_ctor_set(v___x_892_, 3, v___f_890_);
lean_ctor_set(v___x_892_, 4, v___f_889_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v___f_885_);
v___x_894_ = l_StateRefT_x27_instMonad___redArg(v___x_893_);
v_toApplicative_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v___x_894_, 1);
lean_dec(v_unused_956_);
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_955_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_toApplicative_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_955_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_toFunctor_899_; lean_object* v_toSeq_900_; lean_object* v_toSeqLeft_901_; lean_object* v_toSeqRight_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_953_; 
v_toFunctor_899_ = lean_ctor_get(v_toApplicative_895_, 0);
v_toSeq_900_ = lean_ctor_get(v_toApplicative_895_, 2);
v_toSeqLeft_901_ = lean_ctor_get(v_toApplicative_895_, 3);
v_toSeqRight_902_ = lean_ctor_get(v_toApplicative_895_, 4);
v_isSharedCheck_953_ = !lean_is_exclusive(v_toApplicative_895_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v_toApplicative_895_, 1);
lean_dec(v_unused_954_);
v___x_904_ = v_toApplicative_895_;
v_isShared_905_ = v_isSharedCheck_953_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_toSeqRight_902_);
lean_inc(v_toSeqLeft_901_);
lean_inc(v_toSeq_900_);
lean_inc(v_toFunctor_899_);
lean_dec(v_toApplicative_895_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_953_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___f_908_; lean_object* v___f_909_; lean_object* v___x_910_; lean_object* v___f_911_; lean_object* v___f_912_; lean_object* v___f_913_; lean_object* v___x_915_; 
v___f_906_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__6));
v___f_907_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__7));
lean_inc_ref(v_toFunctor_899_);
v___f_908_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_908_, 0, v_toFunctor_899_);
v___f_909_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_909_, 0, v_toFunctor_899_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v___f_908_);
lean_ctor_set(v___x_910_, 1, v___f_909_);
v___f_911_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_911_, 0, v_toSeqRight_902_);
v___f_912_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_912_, 0, v_toSeqLeft_901_);
v___f_913_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_913_, 0, v_toSeq_900_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 4, v___f_911_);
lean_ctor_set(v___x_904_, 3, v___f_912_);
lean_ctor_set(v___x_904_, 2, v___f_913_);
lean_ctor_set(v___x_904_, 1, v___f_906_);
lean_ctor_set(v___x_904_, 0, v___x_910_);
v___x_915_ = v___x_904_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v___f_906_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v___f_913_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v___f_912_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v___f_911_);
v___x_915_ = v_reuseFailAlloc_952_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_917_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___f_907_);
lean_ctor_set(v___x_897_, 0, v___x_915_);
v___x_917_ = v___x_897_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___f_907_);
v___x_917_ = v_reuseFailAlloc_951_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_918_ = l_StateRefT_x27_instMonad___redArg(v___x_917_);
v___x_919_ = l_ReaderT_instMonad___redArg(v___x_918_);
v___x_920_ = l_StateRefT_x27_instMonad___redArg(v___x_919_);
v___x_921_ = l_ReaderT_instMonad___redArg(v___x_920_);
v___x_922_ = l_ReaderT_instMonad___redArg(v___x_921_);
v___x_923_ = l_StateRefT_x27_instMonad___redArg(v___x_922_);
v___x_924_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__8));
v___x_925_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_925_, 0, lean_box(0));
lean_closure_set(v___x_925_, 1, lean_box(0));
lean_closure_set(v___x_925_, 2, v___x_923_);
lean_closure_set(v___x_925_, 3, lean_box(0));
lean_closure_set(v___x_925_, 4, lean_box(0));
lean_closure_set(v___x_925_, 5, v___x_924_);
lean_closure_set(v___x_925_, 6, v___f_863_);
v___x_926_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_925_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_942_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_942_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_942_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_942_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_vars_931_; lean_object* v_size_932_; uint8_t v___x_933_; 
v_vars_931_ = lean_ctor_get(v_a_927_, 0);
lean_inc_ref(v_vars_931_);
lean_dec(v_a_927_);
v_size_932_ = lean_ctor_get(v_vars_931_, 2);
v___x_933_ = lean_nat_dec_lt(v_x_865_, v_size_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_936_; 
lean_dec_ref(v_vars_931_);
v___x_934_ = l_outOfBounds___redArg(v___x_864_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_934_);
v___x_936_ = v___x_929_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
else
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = l_Lean_PersistentArray_get_x21___redArg(v___x_864_, v_vars_931_, v_x_865_);
lean_dec_ref(v_vars_931_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_938_);
v___x_940_ = v___x_929_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
v_a_943_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_926_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_926_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1___boxed(lean_object* v___f_957_, lean_object* v___x_958_, lean_object* v_x_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1(v___f_957_, v___x_958_, v_x_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec(v___y_961_);
lean_dec(v___y_960_);
lean_dec(v_x_959_);
lean_dec_ref(v___x_958_);
return v_res_972_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0(void){
_start:
{
lean_object* v___x_973_; lean_object* v___f_974_; lean_object* v___f_975_; 
v___x_973_ = l_Lean_instInhabitedExpr;
v___f_974_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__4));
v___f_975_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1___boxed), 15, 2);
lean_closure_set(v___f_975_, 0, v___f_974_);
lean_closure_set(v___f_975_, 1, v___x_973_);
return v___f_975_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM(void){
_start:
{
lean_object* v___f_976_; 
v___f_976_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0);
return v___f_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(lean_object* v_a_977_, lean_object* v_f_978_, lean_object* v_s_979_){
_start:
{
lean_object* v_structs_980_; lean_object* v_typeIdOf_981_; lean_object* v_exprToStructId_982_; lean_object* v_exprToStructIdEntries_983_; lean_object* v_forbiddenNatModules_984_; lean_object* v_natStructs_985_; lean_object* v_natTypeIdOf_986_; lean_object* v_exprToNatStructId_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v_structs_980_ = lean_ctor_get(v_s_979_, 0);
v_typeIdOf_981_ = lean_ctor_get(v_s_979_, 1);
v_exprToStructId_982_ = lean_ctor_get(v_s_979_, 2);
v_exprToStructIdEntries_983_ = lean_ctor_get(v_s_979_, 3);
v_forbiddenNatModules_984_ = lean_ctor_get(v_s_979_, 4);
v_natStructs_985_ = lean_ctor_get(v_s_979_, 5);
v_natTypeIdOf_986_ = lean_ctor_get(v_s_979_, 6);
v_exprToNatStructId_987_ = lean_ctor_get(v_s_979_, 7);
v___x_988_ = lean_array_get_size(v_structs_980_);
v___x_989_ = lean_nat_dec_lt(v_a_977_, v___x_988_);
if (v___x_989_ == 0)
{
lean_dec_ref(v_f_978_);
return v_s_979_;
}
else
{
lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1001_; 
lean_inc_ref(v_exprToNatStructId_987_);
lean_inc_ref(v_natTypeIdOf_986_);
lean_inc_ref(v_natStructs_985_);
lean_inc_ref(v_forbiddenNatModules_984_);
lean_inc_ref(v_exprToStructIdEntries_983_);
lean_inc_ref(v_exprToStructId_982_);
lean_inc_ref(v_typeIdOf_981_);
lean_inc_ref(v_structs_980_);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_s_979_);
if (v_isSharedCheck_1001_ == 0)
{
lean_object* v_unused_1002_; lean_object* v_unused_1003_; lean_object* v_unused_1004_; lean_object* v_unused_1005_; lean_object* v_unused_1006_; lean_object* v_unused_1007_; lean_object* v_unused_1008_; lean_object* v_unused_1009_; 
v_unused_1002_ = lean_ctor_get(v_s_979_, 7);
lean_dec(v_unused_1002_);
v_unused_1003_ = lean_ctor_get(v_s_979_, 6);
lean_dec(v_unused_1003_);
v_unused_1004_ = lean_ctor_get(v_s_979_, 5);
lean_dec(v_unused_1004_);
v_unused_1005_ = lean_ctor_get(v_s_979_, 4);
lean_dec(v_unused_1005_);
v_unused_1006_ = lean_ctor_get(v_s_979_, 3);
lean_dec(v_unused_1006_);
v_unused_1007_ = lean_ctor_get(v_s_979_, 2);
lean_dec(v_unused_1007_);
v_unused_1008_ = lean_ctor_get(v_s_979_, 1);
lean_dec(v_unused_1008_);
v_unused_1009_ = lean_ctor_get(v_s_979_, 0);
lean_dec(v_unused_1009_);
v___x_991_ = v_s_979_;
v_isShared_992_ = v_isSharedCheck_1001_;
goto v_resetjp_990_;
}
else
{
lean_dec(v_s_979_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1001_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v_v_993_; lean_object* v___x_994_; lean_object* v_xs_x27_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v_v_993_ = lean_array_fget(v_structs_980_, v_a_977_);
v___x_994_ = lean_box(0);
v_xs_x27_995_ = lean_array_fset(v_structs_980_, v_a_977_, v___x_994_);
v___x_996_ = lean_apply_1(v_f_978_, v_v_993_);
v___x_997_ = lean_array_fset(v_xs_x27_995_, v_a_977_, v___x_996_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_997_);
v___x_999_ = v___x_991_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_typeIdOf_981_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_exprToStructId_982_);
lean_ctor_set(v_reuseFailAlloc_1000_, 3, v_exprToStructIdEntries_983_);
lean_ctor_set(v_reuseFailAlloc_1000_, 4, v_forbiddenNatModules_984_);
lean_ctor_set(v_reuseFailAlloc_1000_, 5, v_natStructs_985_);
lean_ctor_set(v_reuseFailAlloc_1000_, 6, v_natTypeIdOf_986_);
lean_ctor_set(v_reuseFailAlloc_1000_, 7, v_exprToNatStructId_987_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed(lean_object* v_a_1010_, lean_object* v_f_1011_, lean_object* v_s_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(v_a_1010_, v_f_1011_, v_s_1012_);
lean_dec(v_a_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(lean_object* v_f_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_inc(v_a_1015_);
v___f_1018_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1018_, 0, v_a_1015_);
lean_closure_set(v___f_1018_, 1, v_f_1014_);
v___x_1019_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1020_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1019_, v___f_1018_, v_a_1016_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___boxed(lean_object* v_f_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(v_f_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec(v_a_1022_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct(lean_object* v_f_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___f_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_inc(v_a_1027_);
v___f_1039_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1039_, 0, v_a_1027_);
lean_closure_set(v___f_1039_, 1, v_f_1026_);
v___x_1040_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1041_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1040_, v___f_1039_, v_a_1028_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___boxed(lean_object* v_f_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct(v_f_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec(v_a_1043_);
return v_res_1055_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM = _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM);
l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM = _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM);
l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM = _init_l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
}
#ifdef __cplusplus
}
#endif
