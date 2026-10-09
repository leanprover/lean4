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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_5_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_4_, v_a_1_, v_a_2_);
return v___x_5_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_res_6_;
v_res_6_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_1_, v_a_2_);
stack->m_obj
 = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg___boxed(lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_7_, v_a_8_);
lean_dec_ref(v_a_8_);
lean_dec(v_a_7_);
return v_res_10_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27(lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_11_, v_a_19_);
return v___x_22_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_get_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_11_ = stack[0].m_obj;
lean_object* v_a_12_ = stack[1].m_obj;
lean_object* v_a_13_ = stack[2].m_obj;
lean_object* v_a_14_ = stack[3].m_obj;
lean_object* v_a_15_ = stack[4].m_obj;
lean_object* v_a_16_ = stack[5].m_obj;
lean_object* v_a_17_ = stack[6].m_obj;
lean_object* v_a_18_ = stack[7].m_obj;
lean_object* v_a_19_ = stack[8].m_obj;
lean_object* v_a_20_ = stack[9].m_obj;
lean_object* v_res_23_;
v_res_23_ = l_Lean_Meta_Grind_Arith_Linear_get_x27(v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_);
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___boxed(lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Meta_Grind_Arith_Linear_get_x27(v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
lean_dec(v_a_31_);
lean_dec_ref(v_a_30_);
lean_dec(v_a_29_);
lean_dec_ref(v_a_28_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
lean_dec(v_a_25_);
lean_dec(v_a_24_);
return v_res_35_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg(lean_object* v_f_36_, lean_object* v_a_37_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_40_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_39_, v_f_36_, v_a_37_);
return v___x_40_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_36_ = stack[0].m_obj;
lean_object* v_a_37_ = stack[1].m_obj;
lean_object* v_res_41_;
v_res_41_ = l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg(v_f_36_, v_a_37_);
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg___boxed(lean_object* v_f_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Meta_Grind_Arith_Linear_modify_x27___redArg(v_f_42_, v_a_43_);
lean_dec(v_a_43_);
return v_res_45_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27(lean_object* v_f_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_59_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_58_, v_f_46_, v_a_47_);
return v___x_59_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_modify_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_46_ = stack[0].m_obj;
lean_object* v_a_47_ = stack[1].m_obj;
lean_object* v_a_48_ = stack[2].m_obj;
lean_object* v_a_49_ = stack[3].m_obj;
lean_object* v_a_50_ = stack[4].m_obj;
lean_object* v_a_51_ = stack[5].m_obj;
lean_object* v_a_52_ = stack[6].m_obj;
lean_object* v_a_53_ = stack[7].m_obj;
lean_object* v_a_54_ = stack[8].m_obj;
lean_object* v_a_55_ = stack[9].m_obj;
lean_object* v_a_56_ = stack[10].m_obj;
lean_object* v_res_60_;
v_res_60_ = l_Lean_Meta_Grind_Arith_Linear_modify_x27(v_f_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modify_x27___boxed(lean_object* v_f_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Meta_Grind_Arith_Linear_modify_x27(v_f_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec(v_a_62_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift___redArg(lean_object* v_inst_74_, lean_object* v_inst_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_apply_2(v_inst_74_, lean_box(0), v_inst_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfMonadLift(lean_object* v_m_77_, lean_object* v_n_78_, lean_object* v_inst_79_, lean_object* v_inst_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_apply_2(v_inst_79_, lean_box(0), v_inst_80_);
return v___x_81_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg(lean_object* v_structId_82_, lean_object* v_x_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___x_95_; 
lean_inc(v_a_93_);
lean_inc_ref(v_a_92_);
lean_inc(v_a_91_);
lean_inc_ref(v_a_90_);
lean_inc(v_a_89_);
lean_inc_ref(v_a_88_);
lean_inc(v_a_87_);
lean_inc_ref(v_a_86_);
lean_inc(v_a_85_);
lean_inc(v_a_84_);
v___x_95_ = lean_apply_12(v_x_83_, v_structId_82_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, lean_box(0));
return v___x_95_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_structId_82_ = stack[0].m_obj;
lean_object* v_x_83_ = stack[1].m_obj;
lean_object* v_a_84_ = stack[2].m_obj;
lean_object* v_a_85_ = stack[3].m_obj;
lean_object* v_a_86_ = stack[4].m_obj;
lean_object* v_a_87_ = stack[5].m_obj;
lean_object* v_a_88_ = stack[6].m_obj;
lean_object* v_a_89_ = stack[7].m_obj;
lean_object* v_a_90_ = stack[8].m_obj;
lean_object* v_a_91_ = stack[9].m_obj;
lean_object* v_a_92_ = stack[10].m_obj;
lean_object* v_a_93_ = stack[11].m_obj;
lean_object* v_res_96_;
v_res_96_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg(v_structId_82_, v_x_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
stack->m_obj
 = v_res_96_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg___boxed(lean_object* v_structId_97_, lean_object* v_x_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_run___redArg(v_structId_97_, v_x_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec(v_a_100_);
lean_dec(v_a_99_);
return v_res_110_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run(lean_object* v_00_u03b1_111_, lean_object* v_structId_112_, lean_object* v_x_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_125_; 
lean_inc(v_a_123_);
lean_inc_ref(v_a_122_);
lean_inc(v_a_121_);
lean_inc_ref(v_a_120_);
lean_inc(v_a_119_);
lean_inc_ref(v_a_118_);
lean_inc(v_a_117_);
lean_inc_ref(v_a_116_);
lean_inc(v_a_115_);
lean_inc(v_a_114_);
v___x_125_ = lean_apply_12(v_x_113_, v_structId_112_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, lean_box(0));
return v___x_125_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_LinearM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_structId_112_ = stack[1].m_obj;
lean_object* v_x_113_ = stack[2].m_obj;
lean_object* v_a_114_ = stack[3].m_obj;
lean_object* v_a_115_ = stack[4].m_obj;
lean_object* v_a_116_ = stack[5].m_obj;
lean_object* v_a_117_ = stack[6].m_obj;
lean_object* v_a_118_ = stack[7].m_obj;
lean_object* v_a_119_ = stack[8].m_obj;
lean_object* v_a_120_ = stack[9].m_obj;
lean_object* v_a_121_ = stack[10].m_obj;
lean_object* v_a_122_ = stack[11].m_obj;
lean_object* v_a_123_ = stack[12].m_obj;
lean_object* v_res_126_;
v_res_126_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_run(lean_box(0), v_structId_112_, v_x_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_run___boxed(lean_object* v_00_u03b1_127_, lean_object* v_structId_128_, lean_object* v_x_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_run(v_00_u03b1_127_, v_structId_128_, v_x_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec(v_a_130_);
return v_res_141_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg(lean_object* v_a_142_){
_start:
{
lean_object* v___x_144_; 
lean_inc(v_a_142_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v_a_142_);
return v___x_144_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_142_ = stack[0].m_obj;
lean_object* v_res_145_;
v_res_145_ = l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg(v_a_142_);
stack->m_obj
 = v_res_145_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg___boxed(lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Meta_Grind_Arith_Linear_getStructId___redArg(v_a_146_);
lean_dec(v_a_146_);
return v_res_148_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId(lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; 
lean_inc(v_a_149_);
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v_a_149_);
return v___x_161_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getStructId_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_149_ = stack[0].m_obj;
lean_object* v_a_150_ = stack[1].m_obj;
lean_object* v_a_151_ = stack[2].m_obj;
lean_object* v_a_152_ = stack[3].m_obj;
lean_object* v_a_153_ = stack[4].m_obj;
lean_object* v_a_154_ = stack[5].m_obj;
lean_object* v_a_155_ = stack[6].m_obj;
lean_object* v_a_156_ = stack[7].m_obj;
lean_object* v_a_157_ = stack[8].m_obj;
lean_object* v_a_158_ = stack[9].m_obj;
lean_object* v_a_159_ = stack[10].m_obj;
lean_object* v_res_162_;
v_res_162_ = l_Lean_Meta_Grind_Arith_Linear_getStructId(v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId___boxed(lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Meta_Grind_Arith_Linear_getStructId(v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
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
lean_dec(v_a_163_);
return v_res_175_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(lean_object* v_msgData_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; lean_object* v_env_183_; uint8_t v___x_184_; lean_object* v_env_185_; lean_object* v___x_186_; lean_object* v_toCold_187_; lean_object* v_mctx_188_; lean_object* v_lctx_189_; lean_object* v_options_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_182_ = lean_st_ref_get(v___y_180_);
v_env_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc_ref(v_env_183_);
lean_dec(v___x_182_);
v___x_184_ = 0;
v_env_185_ = l_Lean_Environment_setRecordingDeps(v_env_183_, v___x_184_);
v___x_186_ = lean_st_ref_get(v___y_178_);
v_toCold_187_ = lean_ctor_get(v___y_179_, 0);
v_mctx_188_ = lean_ctor_get(v___x_186_, 0);
lean_inc_ref(v_mctx_188_);
lean_dec(v___x_186_);
v_lctx_189_ = lean_ctor_get(v___y_177_, 2);
v_options_190_ = lean_ctor_get(v_toCold_187_, 2);
lean_inc_ref(v_options_190_);
lean_inc_ref(v_lctx_189_);
v___x_191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_191_, 0, v_env_185_);
lean_ctor_set(v___x_191_, 1, v_mctx_188_);
lean_ctor_set(v___x_191_, 2, v_lctx_189_);
lean_ctor_set(v___x_191_, 3, v_options_190_);
v___x_192_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_msgData_176_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_176_ = stack[0].m_obj;
lean_object* v___y_177_ = stack[1].m_obj;
lean_object* v___y_178_ = stack[2].m_obj;
lean_object* v___y_179_ = stack[3].m_obj;
lean_object* v___y_180_ = stack[4].m_obj;
lean_object* v_res_194_;
v_res_194_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msgData_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0___boxed(lean_object* v_msgData_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msgData_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_201_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(lean_object* v_msg_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_ref_208_; lean_object* v___x_209_; lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_218_; 
v_ref_208_ = lean_ctor_get(v___y_205_, 2);
v___x_209_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msg_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_218_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
lean_inc(v_ref_208_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v_ref_208_);
lean_ctor_set(v___x_214_, 1, v_a_210_);
if (v_isShared_213_ == 0)
{
lean_ctor_set_tag(v___x_212_, 1);
lean_ctor_set(v___x_212_, 0, v___x_214_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_202_ = stack[0].m_obj;
lean_object* v___y_203_ = stack[1].m_obj;
lean_object* v___y_204_ = stack[2].m_obj;
lean_object* v___y_205_ = stack[3].m_obj;
lean_object* v___y_206_ = stack[4].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v_msg_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg___boxed(lean_object* v_msg_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v_msg_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
return v_res_226_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0));
v___x_229_ = l_Lean_stringToMessageData(v___x_228_);
return v___x_229_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_231_, v_a_239_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_256_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_256_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_256_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_256_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_structs_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_structs_247_ = lean_ctor_get(v_a_243_, 0);
lean_inc_ref(v_structs_247_);
lean_dec(v_a_243_);
v___x_248_ = lean_array_get_size(v_structs_247_);
v___x_249_ = lean_nat_dec_lt(v_a_230_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec_ref(v_structs_247_);
lean_del_object(v___x_245_);
v___x_250_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1, &l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1);
v___x_251_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_250_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = lean_array_fget(v_structs_247_, v_a_230_);
lean_dec_ref(v_structs_247_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_252_);
v___x_254_ = v___x_245_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
v_a_257_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_242_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_242_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_230_ = stack[0].m_obj;
lean_object* v_a_231_ = stack[1].m_obj;
lean_object* v_a_232_ = stack[2].m_obj;
lean_object* v_a_233_ = stack[3].m_obj;
lean_object* v_a_234_ = stack[4].m_obj;
lean_object* v_a_235_ = stack[5].m_obj;
lean_object* v_a_236_ = stack[6].m_obj;
lean_object* v_a_237_ = stack[7].m_obj;
lean_object* v_a_238_ = stack[8].m_obj;
lean_object* v_a_239_ = stack[9].m_obj;
lean_object* v_a_240_ = stack[10].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___boxed(lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec(v_a_267_);
lean_dec(v_a_266_);
return v_res_278_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(lean_object* v_00_u03b1_279_, lean_object* v_msg_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v_msg_280_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
return v___x_293_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_280_ = stack[1].m_obj;
lean_object* v___y_281_ = stack[2].m_obj;
lean_object* v___y_282_ = stack[3].m_obj;
lean_object* v___y_283_ = stack[4].m_obj;
lean_object* v___y_284_ = stack[5].m_obj;
lean_object* v___y_285_ = stack[6].m_obj;
lean_object* v___y_286_ = stack[7].m_obj;
lean_object* v___y_287_ = stack[8].m_obj;
lean_object* v___y_288_ = stack[9].m_obj;
lean_object* v___y_289_ = stack[10].m_obj;
lean_object* v___y_290_ = stack[11].m_obj;
lean_object* v___y_291_ = stack[12].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(lean_box(0), v_msg_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___boxed(lean_object* v_00_u03b1_295_, lean_object* v_msg_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(v_00_u03b1_295_, v_msg_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec(v___y_298_);
lean_dec(v___y_297_);
return v_res_309_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(lean_object* v_ringId_x3f_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
if (lean_obj_tag(v_ringId_x3f_311_) == 1)
{
lean_object* v_val_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_350_; 
v_val_323_ = lean_ctor_get(v_ringId_x3f_311_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v_ringId_x3f_311_);
if (v_isSharedCheck_350_ == 0)
{
v___x_325_ = v_ringId_x3f_311_;
v_isShared_326_ = v_isSharedCheck_350_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_val_323_);
lean_dec(v_ringId_x3f_311_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_350_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = 0;
v___x_328_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_328_, 0, v_val_323_);
lean_ctor_set_uint8(v___x_328_, sizeof(void*)*1, v___x_327_);
v___x_329_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_328_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
lean_dec_ref_known(v___x_328_, 1);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_341_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_341_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_341_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_341_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_toRing_334_; lean_object* v___x_336_; 
v_toRing_334_ = lean_ctor_get(v_a_330_, 0);
lean_inc_ref(v_toRing_334_);
lean_dec(v_a_330_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v_toRing_334_);
v___x_336_ = v___x_325_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_toRing_334_);
v___x_336_ = v_reuseFailAlloc_340_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_338_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_336_);
v___x_338_ = v___x_332_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_del_object(v___x_325_);
v_a_342_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_329_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_329_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v_ringId_x3f_311_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_ringId_x3f_311_ = stack[0].m_obj;
lean_object* v_a_312_ = stack[1].m_obj;
lean_object* v_a_313_ = stack[2].m_obj;
lean_object* v_a_314_ = stack[3].m_obj;
lean_object* v_a_315_ = stack[4].m_obj;
lean_object* v_a_316_ = stack[5].m_obj;
lean_object* v_a_317_ = stack[6].m_obj;
lean_object* v_a_318_ = stack[7].m_obj;
lean_object* v_a_319_ = stack[8].m_obj;
lean_object* v_a_320_ = stack[9].m_obj;
lean_object* v_a_321_ = stack[10].m_obj;
lean_object* v_res_353_;
v_res_353_ = l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(v_ringId_x3f_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f___boxed(lean_object* v_ringId_x3f_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(v_ringId_x3f_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec(v_a_355_);
return v_res_366_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1);
v___x_376_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_375_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
return v___x_376_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_370_ = stack[0].m_obj;
lean_object* v_a_371_ = stack[1].m_obj;
lean_object* v_a_372_ = stack[2].m_obj;
lean_object* v_a_373_ = stack[3].m_obj;
lean_object* v_res_377_;
v_res_377_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_370_, v_a_371_, v_a_372_, v_a_373_);
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___boxed(lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_378_, v_a_379_, v_a_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
return v_res_383_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing(lean_object* v_00_u03b1_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_392_, v_a_393_, v_a_394_, v_a_395_);
return v___x_397_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_throwNotRing_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_385_ = stack[1].m_obj;
lean_object* v_a_386_ = stack[2].m_obj;
lean_object* v_a_387_ = stack[3].m_obj;
lean_object* v_a_388_ = stack[4].m_obj;
lean_object* v_a_389_ = stack[5].m_obj;
lean_object* v_a_390_ = stack[6].m_obj;
lean_object* v_a_391_ = stack[7].m_obj;
lean_object* v_a_392_ = stack[8].m_obj;
lean_object* v_a_393_ = stack[9].m_obj;
lean_object* v_a_394_ = stack[10].m_obj;
lean_object* v_a_395_ = stack[11].m_obj;
lean_object* v_res_398_;
v_res_398_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing(lean_box(0), v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
stack->m_obj
 = v_res_398_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___boxed(lean_object* v_00_u03b1_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing(v_00_u03b1_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec(v_a_401_);
lean_dec(v_a_400_);
return v_res_412_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0));
v___x_415_ = l_Lean_stringToMessageData(v___x_414_);
return v___x_415_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1);
v___x_422_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_421_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
return v___x_422_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_416_ = stack[0].m_obj;
lean_object* v_a_417_ = stack[1].m_obj;
lean_object* v_a_418_ = stack[2].m_obj;
lean_object* v_a_419_ = stack[3].m_obj;
lean_object* v_res_423_;
v_res_423_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_416_, v_a_417_, v_a_418_, v_a_419_);
stack->m_obj
 = v_res_423_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___boxed(lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_424_, v_a_425_, v_a_426_, v_a_427_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
return v_res_429_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(lean_object* v_00_u03b1_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_438_, v_a_439_, v_a_440_, v_a_441_);
return v___x_443_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_431_ = stack[1].m_obj;
lean_object* v_a_432_ = stack[2].m_obj;
lean_object* v_a_433_ = stack[3].m_obj;
lean_object* v_a_434_ = stack[4].m_obj;
lean_object* v_a_435_ = stack[5].m_obj;
lean_object* v_a_436_ = stack[6].m_obj;
lean_object* v_a_437_ = stack[7].m_obj;
lean_object* v_a_438_ = stack[8].m_obj;
lean_object* v_a_439_ = stack[9].m_obj;
lean_object* v_a_440_ = stack[10].m_obj;
lean_object* v_a_441_ = stack[11].m_obj;
lean_object* v_res_444_;
v_res_444_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(lean_box(0), v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
stack->m_obj
 = v_res_444_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___boxed(lean_object* v_00_u03b1_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(v_00_u03b1_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec(v_a_447_);
lean_dec(v_a_446_);
return v_res_458_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v_ringId_x3f_473_; lean_object* v___x_474_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
v_ringId_x3f_473_ = lean_ctor_get(v_a_472_, 1);
lean_inc(v_ringId_x3f_473_);
lean_dec(v_a_472_);
v___x_474_ = l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(v_ringId_x3f_473_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
return v___x_474_;
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
v_a_475_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_471_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_471_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getRing_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_459_ = stack[0].m_obj;
lean_object* v_a_460_ = stack[1].m_obj;
lean_object* v_a_461_ = stack[2].m_obj;
lean_object* v_a_462_ = stack[3].m_obj;
lean_object* v_a_463_ = stack[4].m_obj;
lean_object* v_a_464_ = stack[5].m_obj;
lean_object* v_a_465_ = stack[6].m_obj;
lean_object* v_a_466_ = stack[7].m_obj;
lean_object* v_a_467_ = stack[8].m_obj;
lean_object* v_a_468_ = stack[9].m_obj;
lean_object* v_a_469_ = stack[10].m_obj;
lean_object* v_res_483_;
v_res_483_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
stack->m_obj
 = v_res_483_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f___boxed(lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
lean_dec(v_a_484_);
return v_res_496_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(lean_object* v_e_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Meta_Sym_canon(v_e_497_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v___x_510_, 1);
v___x_512_ = l_Lean_Meta_Sym_shareCommon(v_a_511_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
return v___x_512_;
}
else
{
return v___x_510_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_497_ = stack[0].m_obj;
lean_object* v___y_498_ = stack[1].m_obj;
lean_object* v___y_499_ = stack[2].m_obj;
lean_object* v___y_500_ = stack[3].m_obj;
lean_object* v___y_501_ = stack[4].m_obj;
lean_object* v___y_502_ = stack[5].m_obj;
lean_object* v___y_503_ = stack[6].m_obj;
lean_object* v___y_504_ = stack[7].m_obj;
lean_object* v___y_505_ = stack[8].m_obj;
lean_object* v___y_506_ = stack[9].m_obj;
lean_object* v___y_507_ = stack[10].m_obj;
lean_object* v___y_508_ = stack[11].m_obj;
lean_object* v_res_513_;
v_res_513_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(v_e_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0___boxed(lean_object* v_e_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(v_e_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec(v___y_516_);
lean_dec(v___y_515_);
return v_res_527_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(lean_object* v_e_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_528_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
return v___x_541_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_528_ = stack[0].m_obj;
lean_object* v___y_529_ = stack[1].m_obj;
lean_object* v___y_530_ = stack[2].m_obj;
lean_object* v___y_531_ = stack[3].m_obj;
lean_object* v___y_532_ = stack[4].m_obj;
lean_object* v___y_533_ = stack[5].m_obj;
lean_object* v___y_534_ = stack[6].m_obj;
lean_object* v___y_535_ = stack[7].m_obj;
lean_object* v___y_536_ = stack[8].m_obj;
lean_object* v___y_537_ = stack[9].m_obj;
lean_object* v___y_538_ = stack[10].m_obj;
lean_object* v___y_539_ = stack[11].m_obj;
lean_object* v_res_542_;
v_res_542_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(v_e_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
stack->m_obj
 = v_res_542_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1___boxed(lean_object* v_e_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(v_e_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec(v___y_545_);
lean_dec(v___y_544_);
return v_res_556_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_585_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_585_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_585_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_585_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
if (lean_obj_tag(v_a_576_) == 1)
{
lean_object* v_val_580_; lean_object* v___x_582_; 
v_val_580_ = lean_ctor_get(v_a_576_, 0);
lean_inc(v_val_580_);
lean_dec_ref_known(v_a_576_, 1);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_val_580_);
v___x_582_ = v___x_578_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_val_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
else
{
lean_object* v___x_584_; 
lean_del_object(v___x_578_);
lean_dec(v_a_576_);
v___x_584_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_570_, v_a_571_, v_a_572_, v_a_573_);
return v___x_584_;
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_a_586_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_575_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_575_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_563_ = stack[0].m_obj;
lean_object* v_a_564_ = stack[1].m_obj;
lean_object* v_a_565_ = stack[2].m_obj;
lean_object* v_a_566_ = stack[3].m_obj;
lean_object* v_a_567_ = stack[4].m_obj;
lean_object* v_a_568_ = stack[5].m_obj;
lean_object* v_a_569_ = stack[6].m_obj;
lean_object* v_a_570_ = stack[7].m_obj;
lean_object* v_a_571_ = stack[8].m_obj;
lean_object* v_a_572_ = stack[9].m_obj;
lean_object* v_a_573_ = stack[10].m_obj;
lean_object* v_res_594_;
v_res_594_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
stack->m_obj
 = v_res_594_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed(lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec(v_a_596_);
lean_dec(v_a_595_);
return v_res_607_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object* v_x_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v_ringId_x3f_623_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v_ringId_x3f_623_ = lean_ctor_get(v_a_622_, 1);
lean_inc(v_ringId_x3f_623_);
lean_dec(v_a_622_);
if (lean_obj_tag(v_ringId_x3f_623_) == 1)
{
lean_object* v_val_624_; uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_val_624_ = lean_ctor_get(v_ringId_x3f_623_, 0);
lean_inc(v_val_624_);
lean_dec_ref_known(v_ringId_x3f_623_, 1);
v___x_625_ = 0;
v___x_626_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_626_, 0, v_val_624_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*1, v___x_625_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
lean_inc(v_a_617_);
lean_inc_ref(v_a_616_);
lean_inc(v_a_615_);
lean_inc_ref(v_a_614_);
lean_inc(v_a_613_);
lean_inc_ref(v_a_612_);
lean_inc(v_a_611_);
lean_inc(v_a_610_);
v___x_627_ = lean_apply_12(v_x_608_, v___x_626_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, lean_box(0));
return v___x_627_;
}
else
{
lean_object* v___x_628_; 
lean_dec(v_ringId_x3f_623_);
lean_dec_ref(v_x_608_);
v___x_628_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_616_, v_a_617_, v_a_618_, v_a_619_);
return v___x_628_;
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v_x_608_);
v_a_629_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_621_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_621_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_608_ = stack[0].m_obj;
lean_object* v_a_609_ = stack[1].m_obj;
lean_object* v_a_610_ = stack[2].m_obj;
lean_object* v_a_611_ = stack[3].m_obj;
lean_object* v_a_612_ = stack[4].m_obj;
lean_object* v_a_613_ = stack[5].m_obj;
lean_object* v_a_614_ = stack[6].m_obj;
lean_object* v_a_615_ = stack[7].m_obj;
lean_object* v_a_616_ = stack[8].m_obj;
lean_object* v_a_617_ = stack[9].m_obj;
lean_object* v_a_618_ = stack[10].m_obj;
lean_object* v_a_619_ = stack[11].m_obj;
lean_object* v_res_637_;
v_res_637_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v_x_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
stack->m_obj
 = v_res_637_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg___boxed(lean_object* v_x_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v_x_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec(v_a_640_);
lean_dec(v_a_639_);
return v_res_651_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM(lean_object* v_00_u03b1_652_, lean_object* v_x_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v_x_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
return v___x_666_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_withRingM_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_653_ = stack[1].m_obj;
lean_object* v_a_654_ = stack[2].m_obj;
lean_object* v_a_655_ = stack[3].m_obj;
lean_object* v_a_656_ = stack[4].m_obj;
lean_object* v_a_657_ = stack[5].m_obj;
lean_object* v_a_658_ = stack[6].m_obj;
lean_object* v_a_659_ = stack[7].m_obj;
lean_object* v_a_660_ = stack[8].m_obj;
lean_object* v_a_661_ = stack[9].m_obj;
lean_object* v_a_662_ = stack[10].m_obj;
lean_object* v_a_663_ = stack[11].m_obj;
lean_object* v_a_664_ = stack[12].m_obj;
lean_object* v_res_667_;
v_res_667_ = l_Lean_Meta_Grind_Arith_Linear_withRingM(lean_box(0), v_x_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
stack->m_obj
 = v_res_667_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___boxed(lean_object* v_00_u03b1_668_, lean_object* v_x_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Meta_Grind_Arith_Linear_withRingM(v_00_u03b1_668_, v_x_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec(v_a_671_);
lean_dec(v_a_670_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0(lean_object* v_f_683_, lean_object* v_s_684_){
_start:
{
lean_object* v_toRing_685_; lean_object* v_invFn_x3f_686_; lean_object* v_divFn_x3f_687_; lean_object* v_semiringId_x3f_688_; lean_object* v_commSemiringInst_689_; lean_object* v_commRingInst_690_; lean_object* v_noZeroDivInst_x3f_691_; lean_object* v_fieldInst_x3f_692_; lean_object* v_powIdentityInst_x3f_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
v_toRing_685_ = lean_ctor_get(v_s_684_, 0);
v_invFn_x3f_686_ = lean_ctor_get(v_s_684_, 1);
v_divFn_x3f_687_ = lean_ctor_get(v_s_684_, 2);
v_semiringId_x3f_688_ = lean_ctor_get(v_s_684_, 3);
v_commSemiringInst_689_ = lean_ctor_get(v_s_684_, 4);
v_commRingInst_690_ = lean_ctor_get(v_s_684_, 5);
v_noZeroDivInst_x3f_691_ = lean_ctor_get(v_s_684_, 6);
v_fieldInst_x3f_692_ = lean_ctor_get(v_s_684_, 7);
v_powIdentityInst_x3f_693_ = lean_ctor_get(v_s_684_, 8);
v_isSharedCheck_701_ = !lean_is_exclusive(v_s_684_);
if (v_isSharedCheck_701_ == 0)
{
v___x_695_ = v_s_684_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_powIdentityInst_x3f_693_);
lean_inc(v_fieldInst_x3f_692_);
lean_inc(v_noZeroDivInst_x3f_691_);
lean_inc(v_commRingInst_690_);
lean_inc(v_commSemiringInst_689_);
lean_inc(v_semiringId_x3f_688_);
lean_inc(v_divFn_x3f_687_);
lean_inc(v_invFn_x3f_686_);
lean_inc(v_toRing_685_);
lean_dec(v_s_684_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_apply_1(v_f_683_, v_toRing_685_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_invFn_x3f_686_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_divFn_x3f_687_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_semiringId_x3f_688_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_commSemiringInst_689_);
lean_ctor_set(v_reuseFailAlloc_700_, 5, v_commRingInst_690_);
lean_ctor_set(v_reuseFailAlloc_700_, 6, v_noZeroDivInst_x3f_691_);
lean_ctor_set(v_reuseFailAlloc_700_, 7, v_fieldInst_x3f_692_);
lean_ctor_set(v_reuseFailAlloc_700_, 8, v_powIdentityInst_x3f_693_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(lean_object* v_f_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___f_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___f_715_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0), 2, 1);
lean_closure_set(v___f_715_, 0, v_f_702_);
v___x_716_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed), 13, 1);
lean_closure_set(v___x_716_, 0, v___f_715_);
v___x_717_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_716_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
return v___x_717_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_702_ = stack[0].m_obj;
lean_object* v___y_703_ = stack[1].m_obj;
lean_object* v___y_704_ = stack[2].m_obj;
lean_object* v___y_705_ = stack[3].m_obj;
lean_object* v___y_706_ = stack[4].m_obj;
lean_object* v___y_707_ = stack[5].m_obj;
lean_object* v___y_708_ = stack[6].m_obj;
lean_object* v___y_709_ = stack[7].m_obj;
lean_object* v___y_710_ = stack[8].m_obj;
lean_object* v___y_711_ = stack[9].m_obj;
lean_object* v___y_712_ = stack[10].m_obj;
lean_object* v___y_713_ = stack[11].m_obj;
lean_object* v_res_718_;
v_res_718_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(v_f_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
stack->m_obj
 = v_res_718_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1___boxed(lean_object* v_f_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(v_f_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec(v___y_721_);
lean_dec(v___y_720_);
return v_res_732_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1(void){
_start:
{
lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___f_734_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0));
v___x_735_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed), 12, 0);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v___f_734_);
return v___x_736_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM(void){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1);
return v___x_737_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0(lean_object* v_____do__lift_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_toRingState_751_; lean_object* v___x_752_; 
v_toRingState_751_ = lean_ctor_get(v_____do__lift_738_, 0);
lean_inc_ref(v_toRingState_751_);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v_toRingState_751_);
return v___x_752_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_738_ = stack[0].m_obj;
lean_object* v___y_739_ = stack[1].m_obj;
lean_object* v___y_740_ = stack[2].m_obj;
lean_object* v___y_741_ = stack[3].m_obj;
lean_object* v___y_742_ = stack[4].m_obj;
lean_object* v___y_743_ = stack[5].m_obj;
lean_object* v___y_744_ = stack[6].m_obj;
lean_object* v___y_745_ = stack[7].m_obj;
lean_object* v___y_746_ = stack[8].m_obj;
lean_object* v___y_747_ = stack[9].m_obj;
lean_object* v___y_748_ = stack[10].m_obj;
lean_object* v___y_749_ = stack[11].m_obj;
lean_object* v_res_753_;
v_res_753_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0(v_____do__lift_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
stack->m_obj
 = v_res_753_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0___boxed(lean_object* v_____do__lift_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0(v_____do__lift_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec_ref(v_____do__lift_754_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__1(lean_object* v_f_768_, lean_object* v_s_769_){
_start:
{
lean_object* v_toRingState_770_; lean_object* v_denoteEntries_771_; lean_object* v_nextId_772_; lean_object* v_steps_773_; lean_object* v_queue_774_; lean_object* v_basis_775_; lean_object* v_diseqs_776_; uint8_t v_recheck_777_; lean_object* v_invSet_778_; lean_object* v_powIdentityVarCount_779_; lean_object* v_numEq0_x3f_780_; uint8_t v_numEq0Updated_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_789_; 
v_toRingState_770_ = lean_ctor_get(v_s_769_, 0);
v_denoteEntries_771_ = lean_ctor_get(v_s_769_, 1);
v_nextId_772_ = lean_ctor_get(v_s_769_, 2);
v_steps_773_ = lean_ctor_get(v_s_769_, 3);
v_queue_774_ = lean_ctor_get(v_s_769_, 4);
v_basis_775_ = lean_ctor_get(v_s_769_, 5);
v_diseqs_776_ = lean_ctor_get(v_s_769_, 6);
v_recheck_777_ = lean_ctor_get_uint8(v_s_769_, sizeof(void*)*10);
v_invSet_778_ = lean_ctor_get(v_s_769_, 7);
v_powIdentityVarCount_779_ = lean_ctor_get(v_s_769_, 8);
v_numEq0_x3f_780_ = lean_ctor_get(v_s_769_, 9);
v_numEq0Updated_781_ = lean_ctor_get_uint8(v_s_769_, sizeof(void*)*10 + 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_s_769_);
if (v_isSharedCheck_789_ == 0)
{
v___x_783_ = v_s_769_;
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_numEq0_x3f_780_);
lean_inc(v_powIdentityVarCount_779_);
lean_inc(v_invSet_778_);
lean_inc(v_diseqs_776_);
lean_inc(v_basis_775_);
lean_inc(v_queue_774_);
lean_inc(v_steps_773_);
lean_inc(v_nextId_772_);
lean_inc(v_denoteEntries_771_);
lean_inc(v_toRingState_770_);
lean_dec(v_s_769_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_785_ = lean_apply_1(v_f_768_, v_toRingState_770_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_785_);
v___x_787_ = v___x_783_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_denoteEntries_771_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_nextId_772_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v_steps_773_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v_queue_774_);
lean_ctor_set(v_reuseFailAlloc_788_, 5, v_basis_775_);
lean_ctor_set(v_reuseFailAlloc_788_, 6, v_diseqs_776_);
lean_ctor_set(v_reuseFailAlloc_788_, 7, v_invSet_778_);
lean_ctor_set(v_reuseFailAlloc_788_, 8, v_powIdentityVarCount_779_);
lean_ctor_set(v_reuseFailAlloc_788_, 9, v_numEq0_x3f_780_);
lean_ctor_set_uint8(v_reuseFailAlloc_788_, sizeof(void*)*10, v_recheck_777_);
lean_ctor_set_uint8(v_reuseFailAlloc_788_, sizeof(void*)*10 + 1, v_numEq0Updated_781_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2(lean_object* v_f_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___f_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___f_803_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__1), 2, 1);
lean_closure_set(v___f_803_, 0, v_f_790_);
v___x_804_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___boxed), 13, 1);
lean_closure_set(v___x_804_, 0, v___f_803_);
v___x_805_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_804_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v___x_805_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_790_ = stack[0].m_obj;
lean_object* v___y_791_ = stack[1].m_obj;
lean_object* v___y_792_ = stack[2].m_obj;
lean_object* v___y_793_ = stack[3].m_obj;
lean_object* v___y_794_ = stack[4].m_obj;
lean_object* v___y_795_ = stack[5].m_obj;
lean_object* v___y_796_ = stack[6].m_obj;
lean_object* v___y_797_ = stack[7].m_obj;
lean_object* v___y_798_ = stack[8].m_obj;
lean_object* v___y_799_ = stack[9].m_obj;
lean_object* v___y_800_ = stack[10].m_obj;
lean_object* v___y_801_ = stack[11].m_obj;
lean_object* v_res_806_;
v_res_806_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2(v_f_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
stack->m_obj
 = v_res_806_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2___boxed(lean_object* v_f_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2(v_f_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec(v___y_809_);
lean_dec(v___y_808_);
return v_res_820_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0(void){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_instMonadEIO___redArg();
return v___x_821_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0);
v___x_823_ = l_StateRefT_x27_instMonad___redArg(v___x_822_);
return v___x_823_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM(void){
_start:
{
lean_object* v___x_831_; lean_object* v_toApplicative_832_; lean_object* v_toFunctor_833_; lean_object* v_toSeq_834_; lean_object* v_toSeqLeft_835_; lean_object* v_toSeqRight_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___f_839_; lean_object* v___f_840_; lean_object* v___x_841_; lean_object* v___f_842_; lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v_toApplicative_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_887_; 
v___x_831_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1);
v_toApplicative_832_ = lean_ctor_get(v___x_831_, 0);
v_toFunctor_833_ = lean_ctor_get(v_toApplicative_832_, 0);
v_toSeq_834_ = lean_ctor_get(v_toApplicative_832_, 2);
v_toSeqLeft_835_ = lean_ctor_get(v_toApplicative_832_, 3);
v_toSeqRight_836_ = lean_ctor_get(v_toApplicative_832_, 4);
v___f_837_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__2));
v___f_838_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__3));
lean_inc_ref_n(v_toFunctor_833_, 2);
v___f_839_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_839_, 0, v_toFunctor_833_);
v___f_840_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_840_, 0, v_toFunctor_833_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v___f_839_);
lean_ctor_set(v___x_841_, 1, v___f_840_);
lean_inc(v_toSeqRight_836_);
v___f_842_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_842_, 0, v_toSeqRight_836_);
lean_inc(v_toSeqLeft_835_);
v___f_843_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_843_, 0, v_toSeqLeft_835_);
lean_inc(v_toSeq_834_);
v___f_844_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_844_, 0, v_toSeq_834_);
v___x_845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_845_, 0, v___x_841_);
lean_ctor_set(v___x_845_, 1, v___f_837_);
lean_ctor_set(v___x_845_, 2, v___f_844_);
lean_ctor_set(v___x_845_, 3, v___f_843_);
lean_ctor_set(v___x_845_, 4, v___f_842_);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___f_838_);
v___x_847_ = l_StateRefT_x27_instMonad___redArg(v___x_846_);
v_toApplicative_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; 
v_unused_888_ = lean_ctor_get(v___x_847_, 1);
lean_dec(v_unused_888_);
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_887_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_toApplicative_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_887_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_toFunctor_852_; lean_object* v_toSeq_853_; lean_object* v_toSeqLeft_854_; lean_object* v_toSeqRight_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_885_; 
v_toFunctor_852_ = lean_ctor_get(v_toApplicative_848_, 0);
v_toSeq_853_ = lean_ctor_get(v_toApplicative_848_, 2);
v_toSeqLeft_854_ = lean_ctor_get(v_toApplicative_848_, 3);
v_toSeqRight_855_ = lean_ctor_get(v_toApplicative_848_, 4);
v_isSharedCheck_885_ = !lean_is_exclusive(v_toApplicative_848_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v_toApplicative_848_, 1);
lean_dec(v_unused_886_);
v___x_857_ = v_toApplicative_848_;
v_isShared_858_ = v_isSharedCheck_885_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_toSeqRight_855_);
lean_inc(v_toSeqLeft_854_);
lean_inc(v_toSeq_853_);
lean_inc(v_toFunctor_852_);
lean_dec(v_toApplicative_848_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_885_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___f_859_; lean_object* v___f_860_; lean_object* v___f_861_; lean_object* v___f_862_; lean_object* v___f_863_; lean_object* v___f_864_; lean_object* v___x_865_; lean_object* v___f_866_; lean_object* v___f_867_; lean_object* v___f_868_; lean_object* v___x_870_; 
v___f_859_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__4));
v___f_860_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__5));
v___f_861_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__6));
v___f_862_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__7));
lean_inc_ref(v_toFunctor_852_);
v___f_863_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_863_, 0, v_toFunctor_852_);
v___f_864_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_864_, 0, v_toFunctor_852_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___f_863_);
lean_ctor_set(v___x_865_, 1, v___f_864_);
v___f_866_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_866_, 0, v_toSeqRight_855_);
v___f_867_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_867_, 0, v_toSeqLeft_854_);
v___f_868_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_868_, 0, v_toSeq_853_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 4, v___f_866_);
lean_ctor_set(v___x_857_, 3, v___f_867_);
lean_ctor_set(v___x_857_, 2, v___f_868_);
lean_ctor_set(v___x_857_, 1, v___f_861_);
lean_ctor_set(v___x_857_, 0, v___x_865_);
v___x_870_ = v___x_857_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___f_861_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v___f_868_);
lean_ctor_set(v_reuseFailAlloc_884_, 3, v___f_867_);
lean_ctor_set(v_reuseFailAlloc_884_, 4, v___f_866_);
v___x_870_ = v_reuseFailAlloc_884_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_872_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v___f_862_);
lean_ctor_set(v___x_850_, 0, v___x_870_);
v___x_872_ = v___x_850_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___f_862_);
v___x_872_ = v_reuseFailAlloc_883_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_873_ = l_StateRefT_x27_instMonad___redArg(v___x_872_);
v___x_874_ = l_ReaderT_instMonad___redArg(v___x_873_);
v___x_875_ = l_StateRefT_x27_instMonad___redArg(v___x_874_);
v___x_876_ = l_ReaderT_instMonad___redArg(v___x_875_);
v___x_877_ = l_ReaderT_instMonad___redArg(v___x_876_);
v___x_878_ = l_StateRefT_x27_instMonad___redArg(v___x_877_);
v___x_879_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__8));
v___x_880_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_880_, 0, lean_box(0));
lean_closure_set(v___x_880_, 1, lean_box(0));
lean_closure_set(v___x_880_, 2, v___x_878_);
lean_closure_set(v___x_880_, 3, lean_box(0));
lean_closure_set(v___x_880_, 4, lean_box(0));
lean_closure_set(v___x_880_, 5, v___x_879_);
lean_closure_set(v___x_880_, 6, v___f_859_);
v___x_881_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_withRingM___boxed), 14, 2);
lean_closure_set(v___x_881_, 0, lean_box(0));
lean_closure_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___f_860_);
return v___x_882_;
}
}
}
}
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1(lean_object* v___f_889_, lean_object* v___x_890_, lean_object* v_x_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; lean_object* v_toApplicative_905_; lean_object* v_toFunctor_906_; lean_object* v_toSeq_907_; lean_object* v_toSeqLeft_908_; lean_object* v_toSeqRight_909_; lean_object* v___f_910_; lean_object* v___f_911_; lean_object* v___f_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___f_915_; lean_object* v___f_916_; lean_object* v___f_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v_toApplicative_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_981_; 
v___x_904_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1);
v_toApplicative_905_ = lean_ctor_get(v___x_904_, 0);
v_toFunctor_906_ = lean_ctor_get(v_toApplicative_905_, 0);
v_toSeq_907_ = lean_ctor_get(v_toApplicative_905_, 2);
v_toSeqLeft_908_ = lean_ctor_get(v_toApplicative_905_, 3);
v_toSeqRight_909_ = lean_ctor_get(v_toApplicative_905_, 4);
v___f_910_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__2));
v___f_911_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__3));
lean_inc_ref_n(v_toFunctor_906_, 2);
v___f_912_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_912_, 0, v_toFunctor_906_);
v___f_913_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_913_, 0, v_toFunctor_906_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v___f_912_);
lean_ctor_set(v___x_914_, 1, v___f_913_);
lean_inc(v_toSeqRight_909_);
v___f_915_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_915_, 0, v_toSeqRight_909_);
lean_inc(v_toSeqLeft_908_);
v___f_916_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_916_, 0, v_toSeqLeft_908_);
lean_inc(v_toSeq_907_);
v___f_917_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_917_, 0, v_toSeq_907_);
v___x_918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_918_, 0, v___x_914_);
lean_ctor_set(v___x_918_, 1, v___f_910_);
lean_ctor_set(v___x_918_, 2, v___f_917_);
lean_ctor_set(v___x_918_, 3, v___f_916_);
lean_ctor_set(v___x_918_, 4, v___f_915_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v___f_911_);
v___x_920_ = l_StateRefT_x27_instMonad___redArg(v___x_919_);
v_toApplicative_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; 
v_unused_982_ = lean_ctor_get(v___x_920_, 1);
lean_dec(v_unused_982_);
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_981_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_toApplicative_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_981_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_toFunctor_925_; lean_object* v_toSeq_926_; lean_object* v_toSeqLeft_927_; lean_object* v_toSeqRight_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_979_; 
v_toFunctor_925_ = lean_ctor_get(v_toApplicative_921_, 0);
v_toSeq_926_ = lean_ctor_get(v_toApplicative_921_, 2);
v_toSeqLeft_927_ = lean_ctor_get(v_toApplicative_921_, 3);
v_toSeqRight_928_ = lean_ctor_get(v_toApplicative_921_, 4);
v_isSharedCheck_979_ = !lean_is_exclusive(v_toApplicative_921_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; 
v_unused_980_ = lean_ctor_get(v_toApplicative_921_, 1);
lean_dec(v_unused_980_);
v___x_930_ = v_toApplicative_921_;
v_isShared_931_ = v_isSharedCheck_979_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_toSeqRight_928_);
lean_inc(v_toSeqLeft_927_);
lean_inc(v_toSeq_926_);
lean_inc(v_toFunctor_925_);
lean_dec(v_toApplicative_921_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_979_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___f_932_; lean_object* v___f_933_; lean_object* v___f_934_; lean_object* v___f_935_; lean_object* v___x_936_; lean_object* v___f_937_; lean_object* v___f_938_; lean_object* v___f_939_; lean_object* v___x_941_; 
v___f_932_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__6));
v___f_933_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__7));
lean_inc_ref(v_toFunctor_925_);
v___f_934_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_934_, 0, v_toFunctor_925_);
v___f_935_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_935_, 0, v_toFunctor_925_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___f_934_);
lean_ctor_set(v___x_936_, 1, v___f_935_);
v___f_937_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_937_, 0, v_toSeqRight_928_);
v___f_938_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_938_, 0, v_toSeqLeft_927_);
v___f_939_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_939_, 0, v_toSeq_926_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 4, v___f_937_);
lean_ctor_set(v___x_930_, 3, v___f_938_);
lean_ctor_set(v___x_930_, 2, v___f_939_);
lean_ctor_set(v___x_930_, 1, v___f_932_);
lean_ctor_set(v___x_930_, 0, v___x_936_);
v___x_941_ = v___x_930_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___f_932_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v___f_939_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v___f_938_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v___f_937_);
v___x_941_ = v_reuseFailAlloc_978_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_943_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 1, v___f_933_);
lean_ctor_set(v___x_923_, 0, v___x_941_);
v___x_943_ = v___x_923_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___f_933_);
v___x_943_ = v_reuseFailAlloc_977_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_944_ = l_StateRefT_x27_instMonad___redArg(v___x_943_);
v___x_945_ = l_ReaderT_instMonad___redArg(v___x_944_);
v___x_946_ = l_StateRefT_x27_instMonad___redArg(v___x_945_);
v___x_947_ = l_ReaderT_instMonad___redArg(v___x_946_);
v___x_948_ = l_ReaderT_instMonad___redArg(v___x_947_);
v___x_949_ = l_StateRefT_x27_instMonad___redArg(v___x_948_);
v___x_950_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__8));
v___x_951_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_951_, 0, lean_box(0));
lean_closure_set(v___x_951_, 1, lean_box(0));
lean_closure_set(v___x_951_, 2, v___x_949_);
lean_closure_set(v___x_951_, 3, lean_box(0));
lean_closure_set(v___x_951_, 4, lean_box(0));
lean_closure_set(v___x_951_, 5, v___x_950_);
lean_closure_set(v___x_951_, 6, v___f_889_);
v___x_952_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_951_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_968_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_968_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_968_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_968_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v_vars_957_; lean_object* v_size_958_; uint8_t v___x_959_; 
v_vars_957_ = lean_ctor_get(v_a_953_, 0);
lean_inc_ref(v_vars_957_);
lean_dec(v_a_953_);
v_size_958_ = lean_ctor_get(v_vars_957_, 2);
v___x_959_ = lean_nat_dec_lt(v_x_891_, v_size_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_962_; 
lean_dec_ref(v_vars_957_);
v___x_960_ = l_outOfBounds___redArg(v___x_890_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_960_);
v___x_962_ = v___x_955_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = l_Lean_PersistentArray_get_x21___redArg(v___x_890_, v_vars_957_, v_x_891_);
lean_dec_ref(v_vars_957_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_964_);
v___x_966_ = v___x_955_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
v_a_969_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_952_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_952_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_889_ = stack[0].m_obj;
lean_object* v___x_890_ = stack[1].m_obj;
lean_object* v_x_891_ = stack[2].m_obj;
lean_object* v___y_892_ = stack[3].m_obj;
lean_object* v___y_893_ = stack[4].m_obj;
lean_object* v___y_894_ = stack[5].m_obj;
lean_object* v___y_895_ = stack[6].m_obj;
lean_object* v___y_896_ = stack[7].m_obj;
lean_object* v___y_897_ = stack[8].m_obj;
lean_object* v___y_898_ = stack[9].m_obj;
lean_object* v___y_899_ = stack[10].m_obj;
lean_object* v___y_900_ = stack[11].m_obj;
lean_object* v___y_901_ = stack[12].m_obj;
lean_object* v___y_902_ = stack[13].m_obj;
lean_object* v_res_983_;
v_res_983_ = l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1(v___f_889_, v___x_890_, v_x_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
stack->m_obj
 = v_res_983_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1___boxed(lean_object* v___f_984_, lean_object* v___x_985_, lean_object* v_x_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1(v___f_984_, v___x_985_, v_x_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec(v___y_988_);
lean_dec(v___y_987_);
lean_dec(v_x_986_);
lean_dec_ref(v___x_985_);
return v_res_999_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___f_1001_; lean_object* v___f_1002_; 
v___x_1000_ = l_Lean_instInhabitedExpr;
v___f_1001_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__4));
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1___boxed), 15, 2);
lean_closure_set(v___f_1002_, 0, v___f_1001_);
lean_closure_set(v___f_1002_, 1, v___x_1000_);
return v___f_1002_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM(void){
_start:
{
lean_object* v___f_1003_; 
v___f_1003_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0);
return v___f_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(lean_object* v_a_1004_, lean_object* v_f_1005_, lean_object* v_s_1006_){
_start:
{
lean_object* v_structs_1007_; lean_object* v_typeIdOf_1008_; lean_object* v_exprToStructId_1009_; lean_object* v_exprToStructIdEntries_1010_; lean_object* v_forbiddenNatModules_1011_; lean_object* v_natStructs_1012_; lean_object* v_natTypeIdOf_1013_; lean_object* v_exprToNatStructId_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v_structs_1007_ = lean_ctor_get(v_s_1006_, 0);
v_typeIdOf_1008_ = lean_ctor_get(v_s_1006_, 1);
v_exprToStructId_1009_ = lean_ctor_get(v_s_1006_, 2);
v_exprToStructIdEntries_1010_ = lean_ctor_get(v_s_1006_, 3);
v_forbiddenNatModules_1011_ = lean_ctor_get(v_s_1006_, 4);
v_natStructs_1012_ = lean_ctor_get(v_s_1006_, 5);
v_natTypeIdOf_1013_ = lean_ctor_get(v_s_1006_, 6);
v_exprToNatStructId_1014_ = lean_ctor_get(v_s_1006_, 7);
v___x_1015_ = lean_array_get_size(v_structs_1007_);
v___x_1016_ = lean_nat_dec_lt(v_a_1004_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_dec_ref(v_f_1005_);
return v_s_1006_;
}
else
{
lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1028_; 
lean_inc_ref(v_exprToNatStructId_1014_);
lean_inc_ref(v_natTypeIdOf_1013_);
lean_inc_ref(v_natStructs_1012_);
lean_inc_ref(v_forbiddenNatModules_1011_);
lean_inc_ref(v_exprToStructIdEntries_1010_);
lean_inc_ref(v_exprToStructId_1009_);
lean_inc_ref(v_typeIdOf_1008_);
lean_inc_ref(v_structs_1007_);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_s_1006_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; lean_object* v_unused_1030_; lean_object* v_unused_1031_; lean_object* v_unused_1032_; lean_object* v_unused_1033_; lean_object* v_unused_1034_; lean_object* v_unused_1035_; lean_object* v_unused_1036_; 
v_unused_1029_ = lean_ctor_get(v_s_1006_, 7);
lean_dec(v_unused_1029_);
v_unused_1030_ = lean_ctor_get(v_s_1006_, 6);
lean_dec(v_unused_1030_);
v_unused_1031_ = lean_ctor_get(v_s_1006_, 5);
lean_dec(v_unused_1031_);
v_unused_1032_ = lean_ctor_get(v_s_1006_, 4);
lean_dec(v_unused_1032_);
v_unused_1033_ = lean_ctor_get(v_s_1006_, 3);
lean_dec(v_unused_1033_);
v_unused_1034_ = lean_ctor_get(v_s_1006_, 2);
lean_dec(v_unused_1034_);
v_unused_1035_ = lean_ctor_get(v_s_1006_, 1);
lean_dec(v_unused_1035_);
v_unused_1036_ = lean_ctor_get(v_s_1006_, 0);
lean_dec(v_unused_1036_);
v___x_1018_ = v_s_1006_;
v_isShared_1019_ = v_isSharedCheck_1028_;
goto v_resetjp_1017_;
}
else
{
lean_dec(v_s_1006_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1028_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_v_1020_; lean_object* v___x_1021_; lean_object* v_xs_x27_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v_v_1020_ = lean_array_fget(v_structs_1007_, v_a_1004_);
v___x_1021_ = lean_box(0);
v_xs_x27_1022_ = lean_array_fset(v_structs_1007_, v_a_1004_, v___x_1021_);
v___x_1023_ = lean_apply_1(v_f_1005_, v_v_1020_);
v___x_1024_ = lean_array_fset(v_xs_x27_1022_, v_a_1004_, v___x_1023_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1024_);
v___x_1026_ = v___x_1018_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_typeIdOf_1008_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v_exprToStructId_1009_);
lean_ctor_set(v_reuseFailAlloc_1027_, 3, v_exprToStructIdEntries_1010_);
lean_ctor_set(v_reuseFailAlloc_1027_, 4, v_forbiddenNatModules_1011_);
lean_ctor_set(v_reuseFailAlloc_1027_, 5, v_natStructs_1012_);
lean_ctor_set(v_reuseFailAlloc_1027_, 6, v_natTypeIdOf_1013_);
lean_ctor_set(v_reuseFailAlloc_1027_, 7, v_exprToNatStructId_1014_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed(lean_object* v_a_1037_, lean_object* v_f_1038_, lean_object* v_s_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(v_a_1037_, v_f_1038_, v_s_1039_);
lean_dec(v_a_1037_);
return v_res_1040_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(lean_object* v_f_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___f_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_inc(v_a_1042_);
v___f_1045_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1045_, 0, v_a_1042_);
lean_closure_set(v___f_1045_, 1, v_f_1041_);
v___x_1046_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1047_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1046_, v___f_1045_, v_a_1043_);
return v___x_1047_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1041_ = stack[0].m_obj;
lean_object* v_a_1042_ = stack[1].m_obj;
lean_object* v_a_1043_ = stack[2].m_obj;
lean_object* v_res_1048_;
v_res_1048_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(v_f_1041_, v_a_1042_, v_a_1043_);
stack->m_obj
 = v_res_1048_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___boxed(lean_object* v_f_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(v_f_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec(v_a_1050_);
return v_res_1053_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct(lean_object* v_f_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___f_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_inc(v_a_1055_);
v___f_1067_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1067_, 0, v_a_1055_);
lean_closure_set(v___f_1067_, 1, v_f_1054_);
v___x_1068_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1069_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1068_, v___f_1067_, v_a_1056_);
return v___x_1069_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_modifyStruct_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1054_ = stack[0].m_obj;
lean_object* v_a_1055_ = stack[1].m_obj;
lean_object* v_a_1056_ = stack[2].m_obj;
lean_object* v_a_1057_ = stack[3].m_obj;
lean_object* v_a_1058_ = stack[4].m_obj;
lean_object* v_a_1059_ = stack[5].m_obj;
lean_object* v_a_1060_ = stack[6].m_obj;
lean_object* v_a_1061_ = stack[7].m_obj;
lean_object* v_a_1062_ = stack[8].m_obj;
lean_object* v_a_1063_ = stack[9].m_obj;
lean_object* v_a_1064_ = stack[10].m_obj;
lean_object* v_a_1065_ = stack[11].m_obj;
lean_object* v_res_1070_;
v_res_1070_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct(v_f_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
stack->m_obj
 = v_res_1070_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___boxed(lean_object* v_f_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct(v_f_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec(v_a_1072_);
return v_res_1084_;
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
