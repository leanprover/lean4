// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Reduction
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic import Lean.Meta.Sym.Simp.Theorems import Lean.Meta.Sym.DSimp
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_evalGround___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__0_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__1_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__1_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__2_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3___boxed, .m_arity = 13, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__2_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__3_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__0_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__8_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__8_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__11;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "  ==>  "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__12_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reductionPass"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 173, 196, 173, 194, 157, 239, 250)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_14_ = lean_apply_12(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0___boxed(lean_object* v_x_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0(v_x_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(lean_object* v_mvarId_29_, lean_object* v_x_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; 
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
lean_inc(v___y_33_);
lean_inc(v___y_32_);
lean_inc_ref(v___y_31_);
v___f_43_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_43_, 0, v_x_30_);
lean_closure_set(v___f_43_, 1, v___y_31_);
lean_closure_set(v___f_43_, 2, v___y_32_);
lean_closure_set(v___f_43_, 3, v___y_33_);
lean_closure_set(v___f_43_, 4, v___y_34_);
lean_closure_set(v___f_43_, 5, v___y_35_);
lean_closure_set(v___f_43_, 6, v___y_36_);
lean_closure_set(v___f_43_, 7, v___y_37_);
v___x_44_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_29_, v___f_43_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
if (lean_obj_tag(v___x_44_) == 0)
{
return v___x_44_;
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_44_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___boxed(lean_object* v_mvarId_53_, lean_object* v_x_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(v_mvarId_53_, v_x_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2(lean_object* v_00_u03b1_68_, lean_object* v_mvarId_69_, lean_object* v_x_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(v_mvarId_69_, v_x_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___boxed(lean_object* v_00_u03b1_84_, lean_object* v_mvarId_85_, lean_object* v_x_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2(v_00_u03b1_84_, v_mvarId_85_, v_x_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0(lean_object* v_x_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___closed__0));
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___boxed(lean_object* v_x_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0(v_x_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v_x_115_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3(lean_object* v___x_127_, lean_object* v___f_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v___x_140_; 
lean_inc_ref(v___y_129_);
v___x_140_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_127_, v___y_129_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_142_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
v___x_142_ = lean_box(0);
if (lean_obj_tag(v_a_141_) == 0)
{
uint8_t v_done_143_; 
v_done_143_ = lean_ctor_get_uint8(v_a_141_, 0);
lean_dec_ref_known(v_a_141_, 0);
if (v_done_143_ == 0)
{
lean_object* v___x_144_; 
lean_dec_ref_known(v___x_140_, 1);
v___x_144_ = lean_apply_12(v___f_128_, v___x_142_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, lean_box(0));
return v___x_144_;
}
else
{
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec_ref(v___f_128_);
return v___x_140_;
}
}
else
{
uint8_t v_done_145_; 
lean_dec_ref(v___y_129_);
v_done_145_ = lean_ctor_get_uint8(v_a_141_, sizeof(void*)*1);
if (v_done_145_ == 0)
{
lean_object* v_e_x27_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_164_; 
lean_dec_ref_known(v___x_140_, 1);
v_e_x27_146_ = lean_ctor_get(v_a_141_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_a_141_);
if (v_isSharedCheck_164_ == 0)
{
v___x_148_ = v_a_141_;
v_isShared_149_ = v_isSharedCheck_164_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_e_x27_146_);
lean_dec(v_a_141_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_164_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; 
lean_inc_ref(v_e_x27_146_);
v___x_150_ = lean_apply_12(v___f_128_, v___x_142_, v_e_x27_146_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, lean_box(0));
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
if (lean_obj_tag(v_a_151_) == 0)
{
lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_162_; 
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; 
v_unused_163_ = lean_ctor_get(v___x_150_, 0);
lean_dec(v_unused_163_);
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_162_;
goto v_resetjp_152_;
}
else
{
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_162_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
uint8_t v_done_155_; lean_object* v___x_157_; 
v_done_155_ = lean_ctor_get_uint8(v_a_151_, 0);
lean_dec_ref_known(v_a_151_, 0);
if (v_isShared_149_ == 0)
{
v___x_157_ = v___x_148_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_e_x27_146_);
v___x_157_ = v_reuseFailAlloc_161_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_159_; 
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*1, v_done_155_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_157_);
v___x_159_ = v___x_153_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_151_, 1);
lean_del_object(v___x_148_);
lean_dec_ref(v_e_x27_146_);
return v___x_150_;
}
}
else
{
lean_del_object(v___x_148_);
lean_dec_ref(v_e_x27_146_);
return v___x_150_;
}
}
}
else
{
lean_dec_ref_known(v_a_141_, 1);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___f_128_);
return v___x_140_;
}
}
}
else
{
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec_ref(v___f_128_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3___boxed(lean_object* v___x_165_, lean_object* v___f_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3(v___x_165_, v___f_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___x_165_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1(lean_object* v_x_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_191_; 
lean_inc_ref(v___y_180_);
v___x_191_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_180_, v___y_186_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_192_);
if (lean_obj_tag(v_a_192_) == 0)
{
uint8_t v_done_193_; 
v_done_193_ = lean_ctor_get_uint8(v_a_192_, 0);
lean_dec_ref_known(v_a_192_, 0);
if (v_done_193_ == 0)
{
lean_object* v___x_194_; 
lean_dec_ref_known(v___x_191_, 1);
v___x_194_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_180_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
return v___x_194_;
}
else
{
lean_dec_ref(v___y_180_);
return v___x_191_;
}
}
else
{
uint8_t v_done_195_; 
lean_dec_ref(v___y_180_);
v_done_195_ = lean_ctor_get_uint8(v_a_192_, sizeof(void*)*1);
if (v_done_195_ == 0)
{
lean_object* v_e_x27_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_214_; 
lean_dec_ref_known(v___x_191_, 1);
v_e_x27_196_ = lean_ctor_get(v_a_192_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_a_192_);
if (v_isSharedCheck_214_ == 0)
{
v___x_198_ = v_a_192_;
v_isShared_199_ = v_isSharedCheck_214_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_e_x27_196_);
lean_dec(v_a_192_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_214_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; 
lean_inc_ref(v_e_x27_196_);
v___x_200_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v_e_x27_196_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
if (lean_obj_tag(v_a_201_) == 0)
{
lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_212_; 
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v___x_200_, 0);
lean_dec(v_unused_213_);
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_212_;
goto v_resetjp_202_;
}
else
{
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_212_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
uint8_t v_done_205_; lean_object* v___x_207_; 
v_done_205_ = lean_ctor_get_uint8(v_a_201_, 0);
lean_dec_ref_known(v_a_201_, 0);
if (v_isShared_199_ == 0)
{
v___x_207_ = v___x_198_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_e_x27_196_);
v___x_207_ = v_reuseFailAlloc_211_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_209_; 
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*1, v_done_205_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_207_);
v___x_209_ = v___x_203_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_201_, 1);
lean_del_object(v___x_198_);
lean_dec_ref(v_e_x27_196_);
return v___x_200_;
}
}
else
{
lean_del_object(v___x_198_);
lean_dec_ref(v_e_x27_196_);
return v___x_200_;
}
}
}
else
{
lean_dec_ref_known(v_a_192_, 1);
return v___x_191_;
}
}
}
else
{
lean_dec_ref(v___y_180_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1___boxed(lean_object* v_x_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1(v_x_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(lean_object* v_msgData_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; lean_object* v_env_235_; lean_object* v___x_236_; lean_object* v_toCold_237_; lean_object* v_mctx_238_; lean_object* v_lctx_239_; lean_object* v_options_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_234_ = lean_st_ref_get(v___y_232_);
v_env_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc_ref(v_env_235_);
lean_dec(v___x_234_);
v___x_236_ = lean_st_ref_get(v___y_230_);
v_toCold_237_ = lean_ctor_get(v___y_231_, 0);
v_mctx_238_ = lean_ctor_get(v___x_236_, 0);
lean_inc_ref(v_mctx_238_);
lean_dec(v___x_236_);
v_lctx_239_ = lean_ctor_get(v___y_229_, 2);
v_options_240_ = lean_ctor_get(v_toCold_237_, 2);
lean_inc_ref(v_options_240_);
lean_inc_ref(v_lctx_239_);
v___x_241_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_241_, 0, v_env_235_);
lean_ctor_set(v___x_241_, 1, v_mctx_238_);
lean_ctor_set(v___x_241_, 2, v_lctx_239_);
lean_ctor_set(v___x_241_, 3, v_options_240_);
v___x_242_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v_msgData_228_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0___boxed(lean_object* v_msgData_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(v_msgData_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
return v_res_250_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_251_; double v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_float_of_nat(v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(lean_object* v_cls_256_, lean_object* v_msg_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_ref_263_; lean_object* v___x_264_; lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_309_; 
v_ref_263_ = lean_ctor_get(v___y_260_, 2);
v___x_264_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(v_msg_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_309_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_309_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_309_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v_traceState_270_; lean_object* v_env_271_; lean_object* v_nextMacroScope_272_; lean_object* v_ngen_273_; lean_object* v_auxDeclNGen_274_; lean_object* v_cache_275_; lean_object* v_messages_276_; lean_object* v_infoState_277_; lean_object* v_snapshotTasks_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_308_; 
v___x_269_ = lean_st_ref_take(v___y_261_);
v_traceState_270_ = lean_ctor_get(v___x_269_, 4);
v_env_271_ = lean_ctor_get(v___x_269_, 0);
v_nextMacroScope_272_ = lean_ctor_get(v___x_269_, 1);
v_ngen_273_ = lean_ctor_get(v___x_269_, 2);
v_auxDeclNGen_274_ = lean_ctor_get(v___x_269_, 3);
v_cache_275_ = lean_ctor_get(v___x_269_, 5);
v_messages_276_ = lean_ctor_get(v___x_269_, 6);
v_infoState_277_ = lean_ctor_get(v___x_269_, 7);
v_snapshotTasks_278_ = lean_ctor_get(v___x_269_, 8);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_308_ == 0)
{
v___x_280_ = v___x_269_;
v_isShared_281_ = v_isSharedCheck_308_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_snapshotTasks_278_);
lean_inc(v_infoState_277_);
lean_inc(v_messages_276_);
lean_inc(v_cache_275_);
lean_inc(v_traceState_270_);
lean_inc(v_auxDeclNGen_274_);
lean_inc(v_ngen_273_);
lean_inc(v_nextMacroScope_272_);
lean_inc(v_env_271_);
lean_dec(v___x_269_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_308_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
uint64_t v_tid_282_; lean_object* v_traces_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_307_; 
v_tid_282_ = lean_ctor_get_uint64(v_traceState_270_, sizeof(void*)*1);
v_traces_283_ = lean_ctor_get(v_traceState_270_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v_traceState_270_);
if (v_isSharedCheck_307_ == 0)
{
v___x_285_ = v_traceState_270_;
v_isShared_286_ = v_isSharedCheck_307_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_traces_283_);
lean_dec(v_traceState_270_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_307_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; double v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_287_ = lean_box(0);
v___x_288_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0);
v___x_289_ = 0;
v___x_290_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__1));
v___x_291_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_291_, 0, v_cls_256_);
lean_ctor_set(v___x_291_, 1, v___x_287_);
lean_ctor_set(v___x_291_, 2, v___x_290_);
lean_ctor_set_float(v___x_291_, sizeof(void*)*3, v___x_288_);
lean_ctor_set_float(v___x_291_, sizeof(void*)*3 + 8, v___x_288_);
lean_ctor_set_uint8(v___x_291_, sizeof(void*)*3 + 16, v___x_289_);
v___x_292_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__2));
v___x_293_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v_a_265_);
lean_ctor_set(v___x_293_, 2, v___x_292_);
lean_inc(v_ref_263_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v_ref_263_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = l_Lean_PersistentArray_push___redArg(v_traces_283_, v___x_294_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_295_);
v___x_297_ = v___x_285_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_295_);
lean_ctor_set_uint64(v_reuseFailAlloc_306_, sizeof(void*)*1, v_tid_282_);
v___x_297_ = v_reuseFailAlloc_306_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_299_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 4, v___x_297_);
v___x_299_ = v___x_280_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_env_271_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_nextMacroScope_272_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v_ngen_273_);
lean_ctor_set(v_reuseFailAlloc_305_, 3, v_auxDeclNGen_274_);
lean_ctor_set(v_reuseFailAlloc_305_, 4, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_305_, 5, v_cache_275_);
lean_ctor_set(v_reuseFailAlloc_305_, 6, v_messages_276_);
lean_ctor_set(v_reuseFailAlloc_305_, 7, v_infoState_277_);
lean_ctor_set(v_reuseFailAlloc_305_, 8, v_snapshotTasks_278_);
v___x_299_ = v_reuseFailAlloc_305_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_300_ = lean_st_ref_put(v___y_261_, v___x_299_);
v___x_301_ = lean_box(0);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_301_);
v___x_303_ = v___x_267_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___boxed(lean_object* v_cls_310_, lean_object* v_msg_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v_cls_310_, v_msg_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(lean_object* v_snd_318_, lean_object* v_a_319_, lean_object* v___x_320_, lean_object* v_____r_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_334_ = lean_array_push(v_snd_318_, v_a_319_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_320_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4___boxed(lean_object* v_snd_338_, lean_object* v_a_339_, lean_object* v___x_340_, lean_object* v_____r_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(v_snd_338_, v_a_339_, v___x_340_, v_____r_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2(lean_object* v___f_355_, lean_object* v_x_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; 
lean_inc_ref(v___y_357_);
v___x_368_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_357_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_370_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
v___x_370_ = lean_box(0);
if (lean_obj_tag(v_a_369_) == 0)
{
uint8_t v_done_371_; 
v_done_371_ = lean_ctor_get_uint8(v_a_369_, 0);
lean_dec_ref_known(v_a_369_, 0);
if (v_done_371_ == 0)
{
lean_object* v___x_372_; 
lean_dec_ref_known(v___x_368_, 1);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc(v___y_364_);
lean_inc_ref(v___y_363_);
lean_inc(v___y_362_);
lean_inc_ref(v___y_361_);
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
v___x_372_ = lean_apply_12(v___f_355_, v___x_370_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, lean_box(0));
return v___x_372_;
}
else
{
lean_dec_ref(v___y_357_);
lean_dec_ref(v___f_355_);
return v___x_368_;
}
}
else
{
uint8_t v_done_373_; 
lean_dec_ref(v___y_357_);
v_done_373_ = lean_ctor_get_uint8(v_a_369_, sizeof(void*)*1);
if (v_done_373_ == 0)
{
lean_object* v_e_x27_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_392_; 
lean_dec_ref_known(v___x_368_, 1);
v_e_x27_374_ = lean_ctor_get(v_a_369_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v_a_369_);
if (v_isSharedCheck_392_ == 0)
{
v___x_376_ = v_a_369_;
v_isShared_377_ = v_isSharedCheck_392_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_e_x27_374_);
lean_dec(v_a_369_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_392_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; 
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc(v___y_364_);
lean_inc_ref(v___y_363_);
lean_inc(v___y_362_);
lean_inc_ref(v___y_361_);
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
lean_inc_ref(v_e_x27_374_);
v___x_378_ = lean_apply_12(v___f_355_, v___x_370_, v_e_x27_374_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, lean_box(0));
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
if (lean_obj_tag(v_a_379_) == 0)
{
lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_390_; 
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v___x_378_, 0);
lean_dec(v_unused_391_);
v___x_381_ = v___x_378_;
v_isShared_382_ = v_isSharedCheck_390_;
goto v_resetjp_380_;
}
else
{
lean_dec(v___x_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_390_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
uint8_t v_done_383_; lean_object* v___x_385_; 
v_done_383_ = lean_ctor_get_uint8(v_a_379_, 0);
lean_dec_ref_known(v_a_379_, 0);
if (v_isShared_377_ == 0)
{
v___x_385_ = v___x_376_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_e_x27_374_);
v___x_385_ = v_reuseFailAlloc_389_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_387_; 
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*1, v_done_383_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_385_);
v___x_387_ = v___x_381_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_379_, 1);
lean_del_object(v___x_376_);
lean_dec_ref(v_e_x27_374_);
return v___x_378_;
}
}
else
{
lean_del_object(v___x_376_);
lean_dec_ref(v_e_x27_374_);
return v___x_378_;
}
}
}
else
{
lean_dec_ref_known(v_a_369_, 1);
lean_dec_ref(v___f_355_);
return v___x_368_;
}
}
}
else
{
lean_dec_ref(v___y_357_);
lean_dec_ref(v___f_355_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2___boxed(lean_object* v___f_393_, lean_object* v_x_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2(v___f_393_, v_x_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(uint8_t v___x_407_, lean_object* v___f_408_, lean_object* v_____r_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; lean_object* v_caches_423_; lean_object* v_typeAnalysis_424_; lean_object* v_target_425_; lean_object* v_hypotheses_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_436_; 
v___x_422_ = lean_st_ref_take(v___y_411_);
v_caches_423_ = lean_ctor_get(v___x_422_, 0);
v_typeAnalysis_424_ = lean_ctor_get(v___x_422_, 1);
v_target_425_ = lean_ctor_get(v___x_422_, 2);
v_hypotheses_426_ = lean_ctor_get(v___x_422_, 3);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_436_ == 0)
{
v___x_428_ = v___x_422_;
v_isShared_429_ = v_isSharedCheck_436_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_hypotheses_426_);
lean_inc(v_target_425_);
lean_inc(v_typeAnalysis_424_);
lean_inc(v_caches_423_);
lean_dec(v___x_422_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_436_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_caches_423_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_typeAnalysis_424_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_target_425_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_hypotheses_426_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*4, v___x_407_);
v___x_432_ = lean_st_ref_put(v___y_411_, v___x_431_);
v___x_433_ = lean_box(0);
lean_inc(v___y_420_);
lean_inc_ref(v___y_419_);
lean_inc(v___y_418_);
lean_inc_ref(v___y_417_);
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
lean_inc(v___y_414_);
lean_inc_ref(v___y_413_);
lean_inc(v___y_412_);
lean_inc(v___y_411_);
lean_inc_ref(v___y_410_);
v___x_434_ = lean_apply_13(v___f_408_, v___x_433_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, lean_box(0));
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5___boxed(lean_object* v___x_437_, lean_object* v___f_438_, lean_object* v_____r_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
uint8_t v___x_11361__boxed_452_; lean_object* v_res_453_; 
v___x_11361__boxed_452_ = lean_unbox(v___x_437_);
v_res_453_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(v___x_11361__boxed_452_, v___f_438_, v_____r_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_453_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__11(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__8));
v___x_475_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10));
v___x_476_ = l_Lean_Name_append(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__12));
v___x_479_ = l_Lean_stringToMessageData(v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(lean_object* v_upperBound_480_, lean_object* v___x_481_, lean_object* v_config_482_, lean_object* v_a_483_, lean_object* v_b_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___y_498_; uint8_t v___x_520_; 
v___x_520_ = lean_nat_dec_lt(v_a_483_, v_upperBound_480_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
lean_dec(v_a_483_);
lean_dec_ref(v_config_482_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v_b_484_);
return v___x_521_;
}
else
{
uint8_t v___x_522_; lean_object* v_methods_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_522_ = 1;
v_methods_523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__4));
v___x_524_ = lean_array_fget_borrowed(v___x_481_, v_a_483_);
lean_inc(v___x_524_);
lean_inc_ref(v_config_482_);
v___x_525_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v___x_522_, v_methods_523_, v_config_482_, v___x_524_, v___y_486_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v_snd_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_590_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v_snd_527_ = lean_ctor_get(v_b_484_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_b_484_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v_b_484_, 0);
lean_dec(v_unused_591_);
v___x_529_ = v_b_484_;
v_isShared_530_ = v_isSharedCheck_590_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_snd_527_);
lean_dec(v_b_484_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_590_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_type_531_; lean_object* v_value_532_; uint8_t v___x_533_; 
v_type_531_ = lean_ctor_get(v_a_526_, 1);
v_value_532_ = lean_ctor_get(v_a_526_, 2);
lean_inc_ref(v_type_531_);
v___x_533_ = l_Lean_Expr_isFalse(v_type_531_);
if (v___x_533_ == 0)
{
lean_object* v_type_534_; lean_object* v___x_535_; lean_object* v___f_536_; uint8_t v___x_565_; 
lean_del_object(v___x_529_);
v_type_534_ = lean_ctor_get(v___x_524_, 1);
v___x_535_ = lean_box(0);
lean_inc(v_a_526_);
lean_inc(v_snd_527_);
v___f_536_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4___boxed), 16, 3);
lean_closure_set(v___f_536_, 0, v_snd_527_);
lean_closure_set(v___f_536_, 1, v_a_526_);
lean_closure_set(v___f_536_, 2, v___x_535_);
v___x_565_ = lean_expr_eqv(v_type_534_, v_type_531_);
if (v___x_565_ == 0)
{
lean_inc_ref(v_type_531_);
lean_dec(v_snd_527_);
lean_dec(v_a_526_);
goto v___jp_540_;
}
else
{
if (v___x_533_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref(v___f_536_);
v___x_566_ = lean_box(0);
v___x_567_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(v_snd_527_, v_a_526_, v___x_535_, v___x_566_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
v___y_498_ = v___x_567_;
goto v___jp_497_;
}
else
{
lean_inc_ref(v_type_531_);
lean_dec(v_snd_527_);
lean_dec(v_a_526_);
goto v___jp_540_;
}
}
v___jp_537_:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_box(0);
v___x_539_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(v___x_520_, v___f_536_, v___x_538_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
v___y_498_ = v___x_539_;
goto v___jp_497_;
}
v___jp_540_:
{
lean_object* v_toCold_541_; lean_object* v_options_542_; uint8_t v_hasTrace_543_; 
v_toCold_541_ = lean_ctor_get(v___y_494_, 0);
v_options_542_ = lean_ctor_get(v_toCold_541_, 2);
v_hasTrace_543_ = lean_ctor_get_uint8(v_options_542_, sizeof(void*)*1);
if (v_hasTrace_543_ == 0)
{
lean_dec_ref(v_type_531_);
goto v___jp_537_;
}
else
{
lean_object* v_inheritedTraceOptions_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_inheritedTraceOptions_544_ = lean_ctor_get(v_toCold_541_, 11);
v___x_545_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__8));
v___x_546_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__11);
v___x_547_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_544_, v_options_542_, v___x_546_);
if (v___x_547_ == 0)
{
lean_dec_ref(v_type_531_);
goto v___jp_537_;
}
else
{
lean_object* v_type_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_type_548_ = lean_ctor_get(v___x_524_, 1);
lean_inc_ref(v_type_548_);
v___x_549_ = l_Lean_MessageData_ofExpr(v_type_548_);
v___x_550_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13);
v___x_551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = l_Lean_MessageData_ofExpr(v_type_531_);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v___x_545_, v___x_553_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_556_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v___x_556_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(v___x_520_, v___f_536_, v_a_555_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
v___y_498_ = v___x_556_;
goto v___jp_497_;
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec_ref(v___f_536_);
lean_dec(v_a_483_);
lean_dec_ref(v_config_482_);
v_a_557_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_554_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_554_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_568_; 
lean_inc_ref(v_value_532_);
lean_dec(v_a_526_);
lean_dec(v_a_483_);
lean_dec_ref(v_config_482_);
v___x_568_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_532_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_580_; 
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v___x_568_, 0);
lean_dec(v_unused_581_);
v___x_570_ = v___x_568_;
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
else
{
lean_dec(v___x_568_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_572_ = lean_box(v___x_520_);
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_573_);
v___x_575_ = v___x_529_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_snd_527_);
v___x_575_ = v_reuseFailAlloc_579_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_577_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_575_);
v___x_577_ = v___x_570_;
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
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_del_object(v___x_529_);
lean_dec(v_snd_527_);
v_a_582_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_568_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_568_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v_b_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_config_482_);
v_a_592_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_525_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_525_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
v___jp_497_:
{
if (lean_obj_tag(v___y_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_511_; 
v_a_499_ = lean_ctor_get(v___y_498_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___y_498_);
if (v_isSharedCheck_511_ == 0)
{
v___x_501_ = v___y_498_;
v_isShared_502_ = v_isSharedCheck_511_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___y_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_511_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
if (lean_obj_tag(v_a_499_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; 
lean_dec(v_a_483_);
lean_dec_ref(v_config_482_);
v_a_503_ = lean_ctor_get(v_a_499_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v_a_499_, 1);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v_a_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
lean_del_object(v___x_501_);
v_a_507_ = lean_ctor_get(v_a_499_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v_a_499_, 1);
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_nat_add(v_a_483_, v___x_508_);
lean_dec(v_a_483_);
v_a_483_ = v___x_509_;
v_b_484_ = v_a_507_;
goto _start;
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec(v_a_483_);
lean_dec_ref(v_config_482_);
v_a_512_ = lean_ctor_get(v___y_498_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___y_498_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___y_498_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___y_498_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_600_ = _args[0];
lean_object* v___x_601_ = _args[1];
lean_object* v_config_602_ = _args[2];
lean_object* v_a_603_ = _args[3];
lean_object* v_b_604_ = _args[4];
lean_object* v___y_605_ = _args[5];
lean_object* v___y_606_ = _args[6];
lean_object* v___y_607_ = _args[7];
lean_object* v___y_608_ = _args[8];
lean_object* v___y_609_ = _args[9];
lean_object* v___y_610_ = _args[10];
lean_object* v___y_611_ = _args[11];
lean_object* v___y_612_ = _args[12];
lean_object* v___y_613_ = _args[13];
lean_object* v___y_614_ = _args[14];
lean_object* v___y_615_ = _args[15];
lean_object* v___y_616_ = _args[16];
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(v_upperBound_600_, v___x_601_, v_config_602_, v_a_603_, v_b_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec_ref(v___x_601_);
lean_dec(v_upperBound_600_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(lean_object* v_config_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; lean_object* v_hypotheses_632_; lean_object* v___x_633_; lean_object* v_newHyps_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_631_ = lean_st_ref_get(v___y_620_);
v_hypotheses_632_ = lean_ctor_get(v___x_631_, 3);
lean_inc_ref(v_hypotheses_632_);
lean_dec(v___x_631_);
v___x_633_ = lean_array_get_size(v_hypotheses_632_);
v_newHyps_634_ = lean_mk_empty_array_with_capacity(v___x_633_);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_box(0);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_newHyps_634_);
v___x_638_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(v___x_633_, v_hypotheses_632_, v_config_618_, v___x_635_, v___x_637_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec_ref(v_hypotheses_632_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_668_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_668_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_668_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_668_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_fst_643_; 
v_fst_643_ = lean_ctor_get(v_a_639_, 0);
if (lean_obj_tag(v_fst_643_) == 0)
{
lean_object* v_snd_644_; lean_object* v___x_645_; lean_object* v_caches_646_; lean_object* v_typeAnalysis_647_; lean_object* v_target_648_; uint8_t v_didChange_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_662_; 
v_snd_644_ = lean_ctor_get(v_a_639_, 1);
lean_inc(v_snd_644_);
lean_dec(v_a_639_);
v___x_645_ = lean_st_ref_take(v___y_620_);
v_caches_646_ = lean_ctor_get(v___x_645_, 0);
v_typeAnalysis_647_ = lean_ctor_get(v___x_645_, 1);
v_target_648_ = lean_ctor_get(v___x_645_, 2);
v_didChange_649_ = lean_ctor_get_uint8(v___x_645_, sizeof(void*)*4);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v___x_645_, 3);
lean_dec(v_unused_663_);
v___x_651_ = v___x_645_;
v_isShared_652_ = v_isSharedCheck_662_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_target_648_);
lean_inc(v_typeAnalysis_647_);
lean_inc(v_caches_646_);
lean_dec(v___x_645_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_662_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 3, v_snd_644_);
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_caches_646_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_typeAnalysis_647_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v_target_648_);
lean_ctor_set(v_reuseFailAlloc_661_, 3, v_snd_644_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*4, v_didChange_649_);
v___x_654_ = v_reuseFailAlloc_661_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; uint8_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_655_ = lean_st_ref_put(v___y_620_, v___x_654_);
v___x_656_ = 0;
v___x_657_ = lean_box(v___x_656_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_657_);
v___x_659_ = v___x_641_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
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
else
{
lean_object* v_val_664_; lean_object* v___x_666_; 
lean_inc_ref(v_fst_643_);
lean_dec(v_a_639_);
v_val_664_ = lean_ctor_get(v_fst_643_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v_fst_643_, 1);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v_val_664_);
v___x_666_ = v___x_641_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_val_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
v_a_669_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_638_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_638_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0___boxed(lean_object* v_config_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(v_config_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_config_703_; lean_object* v___x_704_; lean_object* v_maxSteps_705_; lean_object* v_target_706_; uint8_t v___x_707_; lean_object* v_config_708_; lean_object* v___f_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_config_703_ = lean_ctor_get(v___y_691_, 0);
v___x_704_ = lean_st_ref_get(v___y_692_);
v_maxSteps_705_ = lean_ctor_get(v_config_703_, 1);
v_target_706_ = lean_ctor_get(v___x_704_, 2);
lean_inc_ref(v_target_706_);
lean_dec(v___x_704_);
v___x_707_ = 1;
lean_inc(v_maxSteps_705_);
v_config_708_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_config_708_, 0, v_maxSteps_705_);
lean_ctor_set_uint8(v_config_708_, sizeof(void*)*1, v___x_707_);
v___f_709_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0___boxed), 13, 1);
lean_closure_set(v___f_709_, 0, v_config_708_);
v___x_710_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_706_);
lean_dec_ref(v_target_706_);
v___x_711_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(v___x_710_, v___f_709_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1___boxed(lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(lean_object* v_cls_733_, lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v_cls_733_, v_msg_734_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___boxed(lean_object* v_cls_748_, lean_object* v_msg_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(v_cls_748_, v_msg_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1(lean_object* v_upperBound_763_, lean_object* v___x_764_, lean_object* v_config_765_, lean_object* v_inst_766_, lean_object* v_R_767_, lean_object* v_a_768_, lean_object* v_b_769_, lean_object* v_c_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(v_upperBound_763_, v___x_764_, v_config_765_, v_a_768_, v_b_769_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_784_ = _args[0];
lean_object* v___x_785_ = _args[1];
lean_object* v_config_786_ = _args[2];
lean_object* v_inst_787_ = _args[3];
lean_object* v_R_788_ = _args[4];
lean_object* v_a_789_ = _args[5];
lean_object* v_b_790_ = _args[6];
lean_object* v_c_791_ = _args[7];
lean_object* v___y_792_ = _args[8];
lean_object* v___y_793_ = _args[9];
lean_object* v___y_794_ = _args[10];
lean_object* v___y_795_ = _args[11];
lean_object* v___y_796_ = _args[12];
lean_object* v___y_797_ = _args[13];
lean_object* v___y_798_ = _args[14];
lean_object* v___y_799_ = _args[15];
lean_object* v___y_800_ = _args[16];
lean_object* v___y_801_ = _args[17];
lean_object* v___y_802_ = _args[18];
lean_object* v___y_803_ = _args[19];
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1(v_upperBound_784_, v___x_785_, v_config_786_, v_inst_787_, v_R_788_, v_a_789_, v_b_790_, v_c_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec_ref(v___x_785_);
lean_dec(v_upperBound_784_);
return v_res_804_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(builtin);
}
#ifdef __cplusplus
}
#endif
