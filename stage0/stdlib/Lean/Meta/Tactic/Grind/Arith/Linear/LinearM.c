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
lean_object* v___x_174_; lean_object* v_env_175_; uint8_t v___x_176_; lean_object* v_env_177_; lean_object* v___x_178_; lean_object* v_toCold_179_; lean_object* v_mctx_180_; lean_object* v_lctx_181_; lean_object* v_options_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_174_ = lean_st_ref_get(v___y_172_);
v_env_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc_ref(v_env_175_);
lean_dec(v___x_174_);
v___x_176_ = 0;
v_env_177_ = l_Lean_Environment_setRecordingDeps(v_env_175_, v___x_176_);
v___x_178_ = lean_st_ref_get(v___y_170_);
v_toCold_179_ = lean_ctor_get(v___y_171_, 0);
v_mctx_180_ = lean_ctor_get(v___x_178_, 0);
lean_inc_ref(v_mctx_180_);
lean_dec(v___x_178_);
v_lctx_181_ = lean_ctor_get(v___y_169_, 2);
v_options_182_ = lean_ctor_get(v_toCold_179_, 2);
lean_inc_ref(v_options_182_);
lean_inc_ref(v_lctx_181_);
v___x_183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_183_, 0, v_env_177_);
lean_ctor_set(v___x_183_, 1, v_mctx_180_);
lean_ctor_set(v___x_183_, 2, v_lctx_181_);
lean_ctor_set(v___x_183_, 3, v_options_182_);
v___x_184_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_msgData_168_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0___boxed(lean_object* v_msgData_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msgData_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_ref_199_; lean_object* v___x_200_; lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_209_; 
v_ref_199_ = lean_ctor_get(v___y_196_, 2);
v___x_200_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0_spec__0(v_msg_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_209_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_207_; 
lean_inc(v_ref_199_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v_ref_199_);
lean_ctor_set(v___x_205_, 1, v_a_201_);
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 1);
lean_ctor_set(v___x_203_, 0, v___x_205_);
v___x_207_ = v___x_203_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg___boxed(lean_object* v_msg_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v_msg_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
return v_res_216_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__0));
v___x_219_ = l_Lean_stringToMessageData(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_221_, v_a_229_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_246_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_246_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_246_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_246_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v_structs_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v_structs_237_ = lean_ctor_get(v_a_233_, 0);
lean_inc_ref(v_structs_237_);
lean_dec(v_a_233_);
v___x_238_ = lean_array_get_size(v_structs_237_);
v___x_239_ = lean_nat_dec_lt(v_a_220_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec_ref(v_structs_237_);
lean_del_object(v___x_235_);
v___x_240_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1, &l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___closed__1);
v___x_241_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_240_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_241_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_242_ = lean_array_fget(v_structs_237_, v_a_220_);
lean_dec_ref(v_structs_237_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_242_);
v___x_244_ = v___x_235_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_232_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_232_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct___boxed(lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_a_263_);
lean_dec_ref(v_a_262_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec(v_a_257_);
lean_dec(v_a_256_);
lean_dec(v_a_255_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(lean_object* v_00_u03b1_268_, lean_object* v_msg_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v_msg_269_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___boxed(lean_object* v_00_u03b1_283_, lean_object* v_msg_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0(v_00_u03b1_283_, v_msg_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec(v___y_286_);
lean_dec(v___y_285_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(lean_object* v_ringId_x3f_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
if (lean_obj_tag(v_ringId_x3f_299_) == 1)
{
lean_object* v_val_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_339_; 
v_val_311_ = lean_ctor_get(v_ringId_x3f_299_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v_ringId_x3f_299_);
if (v_isSharedCheck_339_ == 0)
{
v___x_313_ = v_ringId_x3f_299_;
v_isShared_314_ = v_isSharedCheck_339_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_val_311_);
lean_dec(v_ringId_x3f_299_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_339_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_315_ = 0;
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_317_, 0, v_val_311_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*2, v___x_315_);
v___x_318_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___x_317_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
lean_dec_ref_known(v___x_317_, 2);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_330_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_330_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_330_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_330_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_toRing_323_; lean_object* v___x_325_; 
v_toRing_323_ = lean_ctor_get(v_a_319_, 0);
lean_inc_ref(v_toRing_323_);
lean_dec(v_a_319_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v_toRing_323_);
v___x_325_ = v___x_313_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_toRing_323_);
v___x_325_ = v_reuseFailAlloc_329_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_327_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_325_);
v___x_327_ = v___x_321_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_del_object(v___x_313_);
v_a_331_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_318_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_318_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec(v_ringId_x3f_299_);
v___x_340_ = lean_box(0);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f___boxed(lean_object* v_ringId_x3f_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(v_ringId_x3f_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec(v_a_343_);
return v_res_354_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__0));
v___x_357_ = l_Lean_stringToMessageData(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___closed__1);
v___x_364_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_363_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg___boxed(lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing(lean_object* v_00_u03b1_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___boxed(lean_object* v_00_u03b1_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing(v_00_u03b1_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_a_387_);
lean_dec(v_a_386_);
return v_res_398_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__0));
v___x_401_ = l_Lean_stringToMessageData(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___closed__1);
v___x_408_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_LinearM_getStruct_spec__0___redArg(v___x_407_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg___boxed(lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_409_, v_a_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(lean_object* v_00_u03b1_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_423_, v_a_424_, v_a_425_, v_a_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___boxed(lean_object* v_00_u03b1_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing(v_00_u03b1_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec(v_a_431_);
lean_dec(v_a_430_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v_ringId_x3f_457_; lean_object* v___x_458_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
v_ringId_x3f_457_ = lean_ctor_get(v_a_456_, 1);
lean_inc(v_ringId_x3f_457_);
lean_dec(v_a_456_);
v___x_458_ = l_Lean_Meta_Grind_Arith_Linear_getRingCore_x3f(v_ringId_x3f_457_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
return v___x_458_;
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
v_a_459_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_455_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_455_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRing_x3f___boxed(lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec(v_a_468_);
lean_dec(v_a_467_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(lean_object* v_e_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Meta_Sym_canon(v_e_480_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_495_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v___x_495_ = l_Lean_Meta_Sym_shareCommon(v_a_494_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
return v___x_495_;
}
else
{
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0___boxed(lean_object* v_e_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__0(v_e_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec(v___y_498_);
lean_dec(v___y_497_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(lean_object* v_e_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_510_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1___boxed(lean_object* v_e_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Meta_Grind_Arith_Linear_instMonadCanonLinearM___lam__1(v_e_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec(v___y_526_);
lean_dec(v___y_525_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Meta_Grind_Arith_Linear_getRing_x3f(v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_566_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_566_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_566_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_566_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
if (lean_obj_tag(v_a_557_) == 1)
{
lean_object* v_val_561_; lean_object* v___x_563_; 
v_val_561_ = lean_ctor_get(v_a_557_, 0);
lean_inc(v_val_561_);
lean_dec_ref_known(v_a_557_, 1);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v_val_561_);
v___x_563_ = v___x_559_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_val_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
else
{
lean_object* v___x_565_; 
lean_del_object(v___x_559_);
lean_dec(v_a_557_);
v___x_565_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_551_, v_a_552_, v_a_553_, v_a_554_);
return v___x_565_;
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
v_a_567_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_556_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_556_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed(lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec(v_a_576_);
lean_dec(v_a_575_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object* v_x_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v_ringId_x3f_603_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v_ringId_x3f_603_ = lean_ctor_get(v_a_602_, 1);
lean_inc(v_ringId_x3f_603_);
lean_dec(v_a_602_);
if (lean_obj_tag(v_ringId_x3f_603_) == 1)
{
lean_object* v_val_604_; uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_val_604_ = lean_ctor_get(v_ringId_x3f_603_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v_ringId_x3f_603_, 1);
v___x_605_ = 0;
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_607_, 0, v_val_604_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
lean_ctor_set_uint8(v___x_607_, sizeof(void*)*2, v___x_605_);
lean_inc(v_a_599_);
lean_inc_ref(v_a_598_);
lean_inc(v_a_597_);
lean_inc_ref(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_a_594_);
lean_inc(v_a_593_);
lean_inc_ref(v_a_592_);
lean_inc(v_a_591_);
lean_inc(v_a_590_);
v___x_608_ = lean_apply_12(v_x_588_, v___x_607_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, lean_box(0));
return v___x_608_;
}
else
{
lean_object* v___x_609_; 
lean_dec(v_ringId_x3f_603_);
lean_dec_ref(v_x_588_);
v___x_609_ = l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(v_a_596_, v_a_597_, v_a_598_, v_a_599_);
return v___x_609_;
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v_x_588_);
v_a_610_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_601_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_601_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg___boxed(lean_object* v_x_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v_x_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec(v_a_620_);
lean_dec(v_a_619_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM(lean_object* v_00_u03b1_632_, lean_object* v_x_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v_x_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___boxed(lean_object* v_00_u03b1_647_, lean_object* v_x_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Meta_Grind_Arith_Linear_withRingM(v_00_u03b1_647_, v_x_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec(v_a_650_);
lean_dec(v_a_649_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0(lean_object* v_f_662_, lean_object* v_s_663_){
_start:
{
lean_object* v_toRing_664_; lean_object* v_invFn_x3f_665_; lean_object* v_divFn_x3f_666_; lean_object* v_semiringId_x3f_667_; lean_object* v_commSemiringInst_668_; lean_object* v_commRingInst_669_; lean_object* v_noZeroDivInst_x3f_670_; lean_object* v_fieldInst_x3f_671_; lean_object* v_powIdentityInst_x3f_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_680_; 
v_toRing_664_ = lean_ctor_get(v_s_663_, 0);
v_invFn_x3f_665_ = lean_ctor_get(v_s_663_, 1);
v_divFn_x3f_666_ = lean_ctor_get(v_s_663_, 2);
v_semiringId_x3f_667_ = lean_ctor_get(v_s_663_, 3);
v_commSemiringInst_668_ = lean_ctor_get(v_s_663_, 4);
v_commRingInst_669_ = lean_ctor_get(v_s_663_, 5);
v_noZeroDivInst_x3f_670_ = lean_ctor_get(v_s_663_, 6);
v_fieldInst_x3f_671_ = lean_ctor_get(v_s_663_, 7);
v_powIdentityInst_x3f_672_ = lean_ctor_get(v_s_663_, 8);
v_isSharedCheck_680_ = !lean_is_exclusive(v_s_663_);
if (v_isSharedCheck_680_ == 0)
{
v___x_674_ = v_s_663_;
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_powIdentityInst_x3f_672_);
lean_inc(v_fieldInst_x3f_671_);
lean_inc(v_noZeroDivInst_x3f_670_);
lean_inc(v_commRingInst_669_);
lean_inc(v_commSemiringInst_668_);
lean_inc(v_semiringId_x3f_667_);
lean_inc(v_divFn_x3f_666_);
lean_inc(v_invFn_x3f_665_);
lean_inc(v_toRing_664_);
lean_dec(v_s_663_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_apply_1(v_f_662_, v_toRing_664_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_invFn_x3f_665_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_divFn_x3f_666_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_semiringId_x3f_667_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_commSemiringInst_668_);
lean_ctor_set(v_reuseFailAlloc_679_, 5, v_commRingInst_669_);
lean_ctor_set(v_reuseFailAlloc_679_, 6, v_noZeroDivInst_x3f_670_);
lean_ctor_set(v_reuseFailAlloc_679_, 7, v_fieldInst_x3f_671_);
lean_ctor_set(v_reuseFailAlloc_679_, 8, v_powIdentityInst_x3f_672_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(lean_object* v_f_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___f_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___f_694_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__0), 2, 1);
lean_closure_set(v___f_694_, 0, v_f_681_);
v___x_695_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed), 13, 1);
lean_closure_set(v___x_695_, 0, v___f_694_);
v___x_696_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_695_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1___boxed(lean_object* v_f_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___lam__1(v_f_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec(v___y_699_);
lean_dec(v___y_698_);
return v_res_710_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1(void){
_start:
{
lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___f_712_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__0));
v___x_713_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing___boxed), 12, 0);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___f_712_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM(void){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingLinearM___closed__1);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0(lean_object* v_____do__lift_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_toRingState_729_; lean_object* v___x_730_; 
v_toRingState_729_ = lean_ctor_get(v_____do__lift_716_, 0);
lean_inc_ref(v_toRingState_729_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v_toRingState_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0___boxed(lean_object* v_____do__lift_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__0(v_____do__lift_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec_ref(v_____do__lift_731_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__1(lean_object* v_f_745_, lean_object* v_s_746_){
_start:
{
lean_object* v_toRingState_747_; lean_object* v_denoteEntries_748_; lean_object* v_nextId_749_; lean_object* v_steps_750_; lean_object* v_queue_751_; lean_object* v_basis_752_; lean_object* v_diseqs_753_; uint8_t v_recheck_754_; lean_object* v_invSet_755_; lean_object* v_powIdentityVarCount_756_; lean_object* v_numEq0_x3f_757_; uint8_t v_numEq0Updated_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_766_; 
v_toRingState_747_ = lean_ctor_get(v_s_746_, 0);
v_denoteEntries_748_ = lean_ctor_get(v_s_746_, 1);
v_nextId_749_ = lean_ctor_get(v_s_746_, 2);
v_steps_750_ = lean_ctor_get(v_s_746_, 3);
v_queue_751_ = lean_ctor_get(v_s_746_, 4);
v_basis_752_ = lean_ctor_get(v_s_746_, 5);
v_diseqs_753_ = lean_ctor_get(v_s_746_, 6);
v_recheck_754_ = lean_ctor_get_uint8(v_s_746_, sizeof(void*)*10);
v_invSet_755_ = lean_ctor_get(v_s_746_, 7);
v_powIdentityVarCount_756_ = lean_ctor_get(v_s_746_, 8);
v_numEq0_x3f_757_ = lean_ctor_get(v_s_746_, 9);
v_numEq0Updated_758_ = lean_ctor_get_uint8(v_s_746_, sizeof(void*)*10 + 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v_s_746_);
if (v_isSharedCheck_766_ == 0)
{
v___x_760_ = v_s_746_;
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_numEq0_x3f_757_);
lean_inc(v_powIdentityVarCount_756_);
lean_inc(v_invSet_755_);
lean_inc(v_diseqs_753_);
lean_inc(v_basis_752_);
lean_inc(v_queue_751_);
lean_inc(v_steps_750_);
lean_inc(v_nextId_749_);
lean_inc(v_denoteEntries_748_);
lean_inc(v_toRingState_747_);
lean_dec(v_s_746_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = lean_apply_1(v_f_745_, v_toRingState_747_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_762_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_denoteEntries_748_);
lean_ctor_set(v_reuseFailAlloc_765_, 2, v_nextId_749_);
lean_ctor_set(v_reuseFailAlloc_765_, 3, v_steps_750_);
lean_ctor_set(v_reuseFailAlloc_765_, 4, v_queue_751_);
lean_ctor_set(v_reuseFailAlloc_765_, 5, v_basis_752_);
lean_ctor_set(v_reuseFailAlloc_765_, 6, v_diseqs_753_);
lean_ctor_set(v_reuseFailAlloc_765_, 7, v_invSet_755_);
lean_ctor_set(v_reuseFailAlloc_765_, 8, v_powIdentityVarCount_756_);
lean_ctor_set(v_reuseFailAlloc_765_, 9, v_numEq0_x3f_757_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, sizeof(void*)*10, v_recheck_754_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, sizeof(void*)*10 + 1, v_numEq0Updated_758_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2(lean_object* v_f_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___f_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___f_780_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__1), 2, 1);
lean_closure_set(v___f_780_, 0, v_f_767_);
v___x_781_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___boxed), 13, 1);
lean_closure_set(v___x_781_, 0, v___f_780_);
v___x_782_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_781_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2___boxed(lean_object* v_f_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___lam__2(v_f_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec(v___y_785_);
lean_dec(v___y_784_);
return v_res_796_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0(void){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_instMonadEIO___redArg();
return v___x_797_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__0);
v___x_799_ = l_StateRefT_x27_instMonad___redArg(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM(void){
_start:
{
lean_object* v___x_807_; lean_object* v_toApplicative_808_; lean_object* v_toFunctor_809_; lean_object* v_toSeq_810_; lean_object* v_toSeqLeft_811_; lean_object* v_toSeqRight_812_; lean_object* v___f_813_; lean_object* v___f_814_; lean_object* v___f_815_; lean_object* v___f_816_; lean_object* v___x_817_; lean_object* v___f_818_; lean_object* v___f_819_; lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v_toApplicative_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_863_; 
v___x_807_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1);
v_toApplicative_808_ = lean_ctor_get(v___x_807_, 0);
v_toFunctor_809_ = lean_ctor_get(v_toApplicative_808_, 0);
v_toSeq_810_ = lean_ctor_get(v_toApplicative_808_, 2);
v_toSeqLeft_811_ = lean_ctor_get(v_toApplicative_808_, 3);
v_toSeqRight_812_ = lean_ctor_get(v_toApplicative_808_, 4);
v___f_813_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__2));
v___f_814_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__3));
lean_inc_ref_n(v_toFunctor_809_, 2);
v___f_815_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_815_, 0, v_toFunctor_809_);
v___f_816_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_816_, 0, v_toFunctor_809_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v___f_815_);
lean_ctor_set(v___x_817_, 1, v___f_816_);
lean_inc(v_toSeqRight_812_);
v___f_818_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_818_, 0, v_toSeqRight_812_);
lean_inc(v_toSeqLeft_811_);
v___f_819_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_819_, 0, v_toSeqLeft_811_);
lean_inc(v_toSeq_810_);
v___f_820_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_820_, 0, v_toSeq_810_);
v___x_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_821_, 0, v___x_817_);
lean_ctor_set(v___x_821_, 1, v___f_813_);
lean_ctor_set(v___x_821_, 2, v___f_820_);
lean_ctor_set(v___x_821_, 3, v___f_819_);
lean_ctor_set(v___x_821_, 4, v___f_818_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___f_814_);
v___x_823_ = l_StateRefT_x27_instMonad___redArg(v___x_822_);
v_toApplicative_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v___x_823_, 1);
lean_dec(v_unused_864_);
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_863_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_toApplicative_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_863_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_toFunctor_828_; lean_object* v_toSeq_829_; lean_object* v_toSeqLeft_830_; lean_object* v_toSeqRight_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_861_; 
v_toFunctor_828_ = lean_ctor_get(v_toApplicative_824_, 0);
v_toSeq_829_ = lean_ctor_get(v_toApplicative_824_, 2);
v_toSeqLeft_830_ = lean_ctor_get(v_toApplicative_824_, 3);
v_toSeqRight_831_ = lean_ctor_get(v_toApplicative_824_, 4);
v_isSharedCheck_861_ = !lean_is_exclusive(v_toApplicative_824_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v_toApplicative_824_, 1);
lean_dec(v_unused_862_);
v___x_833_ = v_toApplicative_824_;
v_isShared_834_ = v_isSharedCheck_861_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_toSeqRight_831_);
lean_inc(v_toSeqLeft_830_);
lean_inc(v_toSeq_829_);
lean_inc(v_toFunctor_828_);
lean_dec(v_toApplicative_824_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_861_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___f_835_; lean_object* v___f_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___f_839_; lean_object* v___f_840_; lean_object* v___x_841_; lean_object* v___f_842_; lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___x_846_; 
v___f_835_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__4));
v___f_836_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__5));
v___f_837_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__6));
v___f_838_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__7));
lean_inc_ref(v_toFunctor_828_);
v___f_839_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_839_, 0, v_toFunctor_828_);
v___f_840_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_840_, 0, v_toFunctor_828_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v___f_839_);
lean_ctor_set(v___x_841_, 1, v___f_840_);
v___f_842_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_842_, 0, v_toSeqRight_831_);
v___f_843_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_843_, 0, v_toSeqLeft_830_);
v___f_844_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_844_, 0, v_toSeq_829_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 4, v___f_842_);
lean_ctor_set(v___x_833_, 3, v___f_843_);
lean_ctor_set(v___x_833_, 2, v___f_844_);
lean_ctor_set(v___x_833_, 1, v___f_837_);
lean_ctor_set(v___x_833_, 0, v___x_841_);
v___x_846_ = v___x_833_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___f_837_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v___f_844_);
lean_ctor_set(v_reuseFailAlloc_860_, 3, v___f_843_);
lean_ctor_set(v_reuseFailAlloc_860_, 4, v___f_842_);
v___x_846_ = v_reuseFailAlloc_860_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_848_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v___f_838_);
lean_ctor_set(v___x_826_, 0, v___x_846_);
v___x_848_ = v___x_826_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___f_838_);
v___x_848_ = v_reuseFailAlloc_859_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_849_ = l_StateRefT_x27_instMonad___redArg(v___x_848_);
v___x_850_ = l_ReaderT_instMonad___redArg(v___x_849_);
v___x_851_ = l_StateRefT_x27_instMonad___redArg(v___x_850_);
v___x_852_ = l_ReaderT_instMonad___redArg(v___x_851_);
v___x_853_ = l_ReaderT_instMonad___redArg(v___x_852_);
v___x_854_ = l_StateRefT_x27_instMonad___redArg(v___x_853_);
v___x_855_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__8));
v___x_856_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_856_, 0, lean_box(0));
lean_closure_set(v___x_856_, 1, lean_box(0));
lean_closure_set(v___x_856_, 2, v___x_854_);
lean_closure_set(v___x_856_, 3, lean_box(0));
lean_closure_set(v___x_856_, 4, lean_box(0));
lean_closure_set(v___x_856_, 5, v___x_855_);
lean_closure_set(v___x_856_, 6, v___f_835_);
v___x_857_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_withRingM___boxed), 14, 2);
lean_closure_set(v___x_857_, 0, lean_box(0));
lean_closure_set(v___x_857_, 1, v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___f_836_);
return v___x_858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1(lean_object* v___f_865_, lean_object* v___x_866_, lean_object* v_x_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; lean_object* v_toApplicative_881_; lean_object* v_toFunctor_882_; lean_object* v_toSeq_883_; lean_object* v_toSeqLeft_884_; lean_object* v_toSeqRight_885_; lean_object* v___f_886_; lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___f_889_; lean_object* v___x_890_; lean_object* v___f_891_; lean_object* v___f_892_; lean_object* v___f_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_toApplicative_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_957_; 
v___x_880_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__1);
v_toApplicative_881_ = lean_ctor_get(v___x_880_, 0);
v_toFunctor_882_ = lean_ctor_get(v_toApplicative_881_, 0);
v_toSeq_883_ = lean_ctor_get(v_toApplicative_881_, 2);
v_toSeqLeft_884_ = lean_ctor_get(v_toApplicative_881_, 3);
v_toSeqRight_885_ = lean_ctor_get(v_toApplicative_881_, 4);
v___f_886_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__2));
v___f_887_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__3));
lean_inc_ref_n(v_toFunctor_882_, 2);
v___f_888_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_888_, 0, v_toFunctor_882_);
v___f_889_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_889_, 0, v_toFunctor_882_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v___f_888_);
lean_ctor_set(v___x_890_, 1, v___f_889_);
lean_inc(v_toSeqRight_885_);
v___f_891_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_891_, 0, v_toSeqRight_885_);
lean_inc(v_toSeqLeft_884_);
v___f_892_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_892_, 0, v_toSeqLeft_884_);
lean_inc(v_toSeq_883_);
v___f_893_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_893_, 0, v_toSeq_883_);
v___x_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_894_, 0, v___x_890_);
lean_ctor_set(v___x_894_, 1, v___f_886_);
lean_ctor_set(v___x_894_, 2, v___f_893_);
lean_ctor_set(v___x_894_, 3, v___f_892_);
lean_ctor_set(v___x_894_, 4, v___f_891_);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___f_887_);
v___x_896_ = l_StateRefT_x27_instMonad___redArg(v___x_895_);
v_toApplicative_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_957_ == 0)
{
lean_object* v_unused_958_; 
v_unused_958_ = lean_ctor_get(v___x_896_, 1);
lean_dec(v_unused_958_);
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_957_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_toApplicative_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_957_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v_toFunctor_901_; lean_object* v_toSeq_902_; lean_object* v_toSeqLeft_903_; lean_object* v_toSeqRight_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_955_; 
v_toFunctor_901_ = lean_ctor_get(v_toApplicative_897_, 0);
v_toSeq_902_ = lean_ctor_get(v_toApplicative_897_, 2);
v_toSeqLeft_903_ = lean_ctor_get(v_toApplicative_897_, 3);
v_toSeqRight_904_ = lean_ctor_get(v_toApplicative_897_, 4);
v_isSharedCheck_955_ = !lean_is_exclusive(v_toApplicative_897_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v_toApplicative_897_, 1);
lean_dec(v_unused_956_);
v___x_906_ = v_toApplicative_897_;
v_isShared_907_ = v_isSharedCheck_955_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_toSeqRight_904_);
lean_inc(v_toSeqLeft_903_);
lean_inc(v_toSeq_902_);
lean_inc(v_toFunctor_901_);
lean_dec(v_toApplicative_897_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_955_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___f_908_; lean_object* v___f_909_; lean_object* v___f_910_; lean_object* v___f_911_; lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___f_914_; lean_object* v___f_915_; lean_object* v___x_917_; 
v___f_908_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__6));
v___f_909_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__7));
lean_inc_ref(v_toFunctor_901_);
v___f_910_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_910_, 0, v_toFunctor_901_);
v___f_911_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_911_, 0, v_toFunctor_901_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___f_910_);
lean_ctor_set(v___x_912_, 1, v___f_911_);
v___f_913_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_913_, 0, v_toSeqRight_904_);
v___f_914_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_914_, 0, v_toSeqLeft_903_);
v___f_915_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_915_, 0, v_toSeq_902_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 4, v___f_913_);
lean_ctor_set(v___x_906_, 3, v___f_914_);
lean_ctor_set(v___x_906_, 2, v___f_915_);
lean_ctor_set(v___x_906_, 1, v___f_908_);
lean_ctor_set(v___x_906_, 0, v___x_912_);
v___x_917_ = v___x_906_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___f_908_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v___f_915_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v___f_914_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v___f_913_);
v___x_917_ = v_reuseFailAlloc_954_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v___f_909_);
lean_ctor_set(v___x_899_, 0, v___x_917_);
v___x_919_ = v___x_899_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___f_909_);
v___x_919_ = v_reuseFailAlloc_953_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_920_ = l_StateRefT_x27_instMonad___redArg(v___x_919_);
v___x_921_ = l_ReaderT_instMonad___redArg(v___x_920_);
v___x_922_ = l_StateRefT_x27_instMonad___redArg(v___x_921_);
v___x_923_ = l_ReaderT_instMonad___redArg(v___x_922_);
v___x_924_ = l_ReaderT_instMonad___redArg(v___x_923_);
v___x_925_ = l_StateRefT_x27_instMonad___redArg(v___x_924_);
v___x_926_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__8));
v___x_927_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_927_, 0, lean_box(0));
lean_closure_set(v___x_927_, 1, lean_box(0));
lean_closure_set(v___x_927_, 2, v___x_925_);
lean_closure_set(v___x_927_, 3, lean_box(0));
lean_closure_set(v___x_927_, 4, lean_box(0));
lean_closure_set(v___x_927_, 5, v___x_926_);
lean_closure_set(v___x_927_, 6, v___f_865_);
v___x_928_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_927_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_944_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_944_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_944_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_944_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_vars_933_; lean_object* v_size_934_; uint8_t v___x_935_; 
v_vars_933_ = lean_ctor_get(v_a_929_, 0);
lean_inc_ref(v_vars_933_);
lean_dec(v_a_929_);
v_size_934_ = lean_ctor_get(v_vars_933_, 2);
v___x_935_ = lean_nat_dec_lt(v_x_867_, v_size_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_938_; 
lean_dec_ref(v_vars_933_);
v___x_936_ = l_outOfBounds___redArg(v___x_866_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_936_);
v___x_938_ = v___x_931_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_940_ = l_Lean_PersistentArray_get_x21___redArg(v___x_866_, v_vars_933_, v_x_867_);
lean_dec_ref(v_vars_933_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_940_);
v___x_942_ = v___x_931_;
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
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
v_a_945_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_928_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_928_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1___boxed(lean_object* v___f_959_, lean_object* v___x_960_, lean_object* v_x_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1(v___f_959_, v___x_960_, v_x_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec(v___y_963_);
lean_dec(v___y_962_);
lean_dec(v_x_961_);
lean_dec_ref(v___x_960_);
return v_res_974_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0(void){
_start:
{
lean_object* v___x_975_; lean_object* v___f_976_; lean_object* v___f_977_; 
v___x_975_ = l_Lean_instInhabitedExpr;
v___f_976_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instMonadRingStateLinearM___closed__4));
v___f_977_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___lam__1___boxed), 15, 2);
lean_closure_set(v___f_977_, 0, v___f_976_);
lean_closure_set(v___f_977_, 1, v___x_975_);
return v___f_977_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM(void){
_start:
{
lean_object* v___f_978_; 
v___f_978_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instMonadGetVarLinearM___closed__0);
return v___f_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(lean_object* v_a_979_, lean_object* v_f_980_, lean_object* v_s_981_){
_start:
{
lean_object* v_structs_982_; lean_object* v_typeIdOf_983_; lean_object* v_exprToStructId_984_; lean_object* v_exprToStructIdEntries_985_; lean_object* v_forbiddenNatModules_986_; lean_object* v_natStructs_987_; lean_object* v_natTypeIdOf_988_; lean_object* v_exprToNatStructId_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_structs_982_ = lean_ctor_get(v_s_981_, 0);
v_typeIdOf_983_ = lean_ctor_get(v_s_981_, 1);
v_exprToStructId_984_ = lean_ctor_get(v_s_981_, 2);
v_exprToStructIdEntries_985_ = lean_ctor_get(v_s_981_, 3);
v_forbiddenNatModules_986_ = lean_ctor_get(v_s_981_, 4);
v_natStructs_987_ = lean_ctor_get(v_s_981_, 5);
v_natTypeIdOf_988_ = lean_ctor_get(v_s_981_, 6);
v_exprToNatStructId_989_ = lean_ctor_get(v_s_981_, 7);
v___x_990_ = lean_array_get_size(v_structs_982_);
v___x_991_ = lean_nat_dec_lt(v_a_979_, v___x_990_);
if (v___x_991_ == 0)
{
lean_dec_ref(v_f_980_);
return v_s_981_;
}
else
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1003_; 
lean_inc_ref(v_exprToNatStructId_989_);
lean_inc_ref(v_natTypeIdOf_988_);
lean_inc_ref(v_natStructs_987_);
lean_inc_ref(v_forbiddenNatModules_986_);
lean_inc_ref(v_exprToStructIdEntries_985_);
lean_inc_ref(v_exprToStructId_984_);
lean_inc_ref(v_typeIdOf_983_);
lean_inc_ref(v_structs_982_);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_s_981_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; lean_object* v_unused_1005_; lean_object* v_unused_1006_; lean_object* v_unused_1007_; lean_object* v_unused_1008_; lean_object* v_unused_1009_; lean_object* v_unused_1010_; lean_object* v_unused_1011_; 
v_unused_1004_ = lean_ctor_get(v_s_981_, 7);
lean_dec(v_unused_1004_);
v_unused_1005_ = lean_ctor_get(v_s_981_, 6);
lean_dec(v_unused_1005_);
v_unused_1006_ = lean_ctor_get(v_s_981_, 5);
lean_dec(v_unused_1006_);
v_unused_1007_ = lean_ctor_get(v_s_981_, 4);
lean_dec(v_unused_1007_);
v_unused_1008_ = lean_ctor_get(v_s_981_, 3);
lean_dec(v_unused_1008_);
v_unused_1009_ = lean_ctor_get(v_s_981_, 2);
lean_dec(v_unused_1009_);
v_unused_1010_ = lean_ctor_get(v_s_981_, 1);
lean_dec(v_unused_1010_);
v_unused_1011_ = lean_ctor_get(v_s_981_, 0);
lean_dec(v_unused_1011_);
v___x_993_ = v_s_981_;
v_isShared_994_ = v_isSharedCheck_1003_;
goto v_resetjp_992_;
}
else
{
lean_dec(v_s_981_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1003_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_v_995_; lean_object* v___x_996_; lean_object* v_xs_x27_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
v_v_995_ = lean_array_fget(v_structs_982_, v_a_979_);
v___x_996_ = lean_box(0);
v_xs_x27_997_ = lean_array_fset(v_structs_982_, v_a_979_, v___x_996_);
v___x_998_ = lean_apply_1(v_f_980_, v_v_995_);
v___x_999_ = lean_array_fset(v_xs_x27_997_, v_a_979_, v___x_998_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_999_);
v___x_1001_ = v___x_993_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_typeIdOf_983_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_exprToStructId_984_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_exprToStructIdEntries_985_);
lean_ctor_set(v_reuseFailAlloc_1002_, 4, v_forbiddenNatModules_986_);
lean_ctor_set(v_reuseFailAlloc_1002_, 5, v_natStructs_987_);
lean_ctor_set(v_reuseFailAlloc_1002_, 6, v_natTypeIdOf_988_);
lean_ctor_set(v_reuseFailAlloc_1002_, 7, v_exprToNatStructId_989_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed(lean_object* v_a_1012_, lean_object* v_f_1013_, lean_object* v_s_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0(v_a_1012_, v_f_1013_, v_s_1014_);
lean_dec(v_a_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(lean_object* v_f_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___f_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_inc(v_a_1017_);
v___f_1020_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1020_, 0, v_a_1017_);
lean_closure_set(v___f_1020_, 1, v_f_1016_);
v___x_1021_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1022_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1021_, v___f_1020_, v_a_1018_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___boxed(lean_object* v_f_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg(v_f_1023_, v_a_1024_, v_a_1025_);
lean_dec(v_a_1025_);
lean_dec(v_a_1024_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct(lean_object* v_f_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___f_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_inc(v_a_1029_);
v___f_1041_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1041_, 0, v_a_1029_);
lean_closure_set(v___f_1041_, 1, v_f_1028_);
v___x_1042_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1043_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1042_, v___f_1041_, v_a_1030_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_modifyStruct___boxed(lean_object* v_f_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_Meta_Grind_Arith_Linear_modifyStruct(v_f_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec(v_a_1045_);
return v_res_1057_;
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
