// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.SimpAll
// Imports: public import Lean.Meta.Tactic.Simp.Main
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheoremsArray_eraseTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setSimpTheorems(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedOrigin_default;
extern lean_object* l_Lean_instInhabitedFVarId_default;
uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_MVarId_assertHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
static const lean_string_object l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__0 = (const lean_object*)&l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__1 = (const lean_object*)&l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2;
static lean_once_cell_t l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_instInhabitedEntry_default;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_instInhabitedEntry;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "↓ "};
static const lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 4, .m_data = "↓ ← "};
static const lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__3;
static const lean_string_object l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "← "};
static const lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___lam__0___boxed(lean_object**);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__5_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(238, 191, 30, 88, 6, 20, 173, 203)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "entry.id: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__7;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__9;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__11;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_SimpAll_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_SimpAll_main___closed__0 = (const lean_object*)&l_Lean_Meta_SimpAll_main___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_simpAll___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "simp_all made no progress"};
static const lean_object* l_Lean_Meta_simpAll___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_simpAll___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_simpAll___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_simpAll___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_simpAll___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_simpAll___closed__0 = (const lean_object*)&l_Lean_Meta_simpAll___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(203, 9, 234, 253, 232, 127, 99, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "SimpAll"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(29, 213, 72, 64, 71, 193, 146, 44)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(40, 3, 80, 75, 73, 97, 213, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 231, 222, 201, 110, 167, 174, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 169, 0, 235, 118, 49, 137, 5)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(248, 76, 186, 86, 98, 101, 42, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 219, 235, 57, 166, 132, 179, 114)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(140, 232, 35, 40, 194, 216, 253, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 101, 77, 233, 232, 200, 249, 82)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 207, 103, 84, 232, 152, 203, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 176, 134, 74, 196, 115, 113, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 93, 220, 66, 184, 67, 196, 199)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)(((size_t)(816399212) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(88, 120, 139, 198, 148, 13, 137, 50)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 237, 39, 184, 252, 108, 58, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 74, 8, 72, 135, 211, 100, 76)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(82, 156, 118, 24, 13, 231, 86, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_7_ = lean_obj_once(&l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2, &l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2_once, _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2);
v___x_8_ = l_Lean_Meta_instInhabitedOrigin_default;
v___x_9_ = lean_box(0);
v___x_10_ = l_Lean_instInhabitedFVarId_default;
v___x_11_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
lean_ctor_set(v___x_11_, 2, v___x_8_);
lean_ctor_set(v___x_11_, 3, v___x_7_);
lean_ctor_set(v___x_11_, 4, v___x_7_);
lean_ctor_set(v___x_11_, 5, v___x_7_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3, &l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3_once, _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Meta_SimpAll_instInhabitedEntry(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Meta_SimpAll_instInhabitedEntry_default;
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0(lean_object* v_x_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___x_21_; 
lean_inc(v___y_15_);
v___x_21_ = lean_apply_6(v_x_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, lean_box(0));
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0___boxed(lean_object* v_x_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0(v_x_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
lean_dec(v___y_23_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(lean_object* v_mvarId_30_, lean_object* v_x_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___f_38_; lean_object* v___x_39_; 
lean_inc(v___y_32_);
v___f_38_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_38_, 0, v_x_31_);
lean_closure_set(v___f_38_, 1, v___y_32_);
v___x_39_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_30_, v___f_38_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
if (lean_obj_tag(v___x_39_) == 0)
{
return v___x_39_;
}
else
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
v_a_40_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v___x_39_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v___x_39_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___boxed(lean_object* v_mvarId_48_, lean_object* v_x_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_48_, v_x_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0(lean_object* v_00_u03b1_57_, lean_object* v_mvarId_58_, lean_object* v_x_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_58_, v_x_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___boxed(lean_object* v_00_u03b1_67_, lean_object* v_mvarId_68_, lean_object* v_x_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0(v_00_u03b1_67_, v_mvarId_68_, v_x_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(lean_object* v_e_77_, lean_object* v___y_78_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = l_Lean_Expr_hasMVar(v_e_77_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v_e_77_);
return v___x_81_;
}
else
{
lean_object* v___x_82_; lean_object* v_mctx_83_; lean_object* v___x_84_; lean_object* v_fst_85_; lean_object* v_snd_86_; lean_object* v___x_87_; lean_object* v_cache_88_; lean_object* v_zetaDeltaFVarIds_89_; lean_object* v_postponed_90_; lean_object* v_diag_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_100_; 
v___x_82_ = lean_st_ref_get(v___y_78_);
v_mctx_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_mctx_83_);
lean_dec(v___x_82_);
v___x_84_ = l_Lean_instantiateMVarsCore(v_mctx_83_, v_e_77_);
v_fst_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_fst_85_);
v_snd_86_ = lean_ctor_get(v___x_84_, 1);
lean_inc(v_snd_86_);
lean_dec_ref(v___x_84_);
v___x_87_ = lean_st_ref_take(v___y_78_);
v_cache_88_ = lean_ctor_get(v___x_87_, 1);
v_zetaDeltaFVarIds_89_ = lean_ctor_get(v___x_87_, 2);
v_postponed_90_ = lean_ctor_get(v___x_87_, 3);
v_diag_91_ = lean_ctor_get(v___x_87_, 4);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v___x_87_, 0);
lean_dec(v_unused_101_);
v___x_93_ = v___x_87_;
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_diag_91_);
lean_inc(v_postponed_90_);
lean_inc(v_zetaDeltaFVarIds_89_);
lean_inc(v_cache_88_);
lean_dec(v___x_87_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v_snd_86_);
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_snd_86_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_cache_88_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_zetaDeltaFVarIds_89_);
lean_ctor_set(v_reuseFailAlloc_99_, 3, v_postponed_90_);
lean_ctor_set(v_reuseFailAlloc_99_, 4, v_diag_91_);
v___x_96_ = v_reuseFailAlloc_99_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_st_ref_set(v___y_78_, v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v_fst_85_);
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg___boxed(lean_object* v_e_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(v_e_102_, v___y_103_);
lean_dec(v___y_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2(lean_object* v_e_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(v_e_106_, v___y_109_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___boxed(lean_object* v_e_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2(v_e_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0(lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v___x_128_; 
lean_inc_ref(v___y_123_);
v___x_128_ = l_Lean_Meta_getPropHyps(v___y_123_, v___y_124_, v___y_125_, v___y_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0___boxed(lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0(v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
return v_res_135_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(lean_object* v_a_136_, lean_object* v_as_137_, size_t v_i_138_, size_t v_stop_139_){
_start:
{
uint8_t v___x_140_; 
v___x_140_ = lean_usize_dec_eq(v_i_138_, v_stop_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = lean_array_uget_borrowed(v_as_137_, v_i_138_);
v___x_142_ = l_Lean_instBEqFVarId_beq(v_a_136_, v___x_141_);
if (v___x_142_ == 0)
{
size_t v___x_143_; size_t v___x_144_; 
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_add(v_i_138_, v___x_143_);
v_i_138_ = v___x_144_;
goto _start;
}
else
{
return v___x_142_;
}
}
else
{
uint8_t v___x_146_; 
v___x_146_ = 0;
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1___boxed(lean_object* v_a_147_, lean_object* v_as_148_, lean_object* v_i_149_, lean_object* v_stop_150_){
_start:
{
size_t v_i_boxed_151_; size_t v_stop_boxed_152_; uint8_t v_res_153_; lean_object* v_r_154_; 
v_i_boxed_151_ = lean_unbox_usize(v_i_149_);
lean_dec(v_i_149_);
v_stop_boxed_152_ = lean_unbox_usize(v_stop_150_);
lean_dec(v_stop_150_);
v_res_153_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(v_a_147_, v_as_148_, v_i_boxed_151_, v_stop_boxed_152_);
lean_dec_ref(v_as_148_);
lean_dec(v_a_147_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(lean_object* v_as_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_array_get_size(v_as_155_);
v___x_159_ = lean_nat_dec_lt(v___x_157_, v___x_158_);
if (v___x_159_ == 0)
{
return v___x_159_;
}
else
{
if (v___x_159_ == 0)
{
return v___x_159_;
}
else
{
size_t v___x_160_; size_t v___x_161_; uint8_t v___x_162_; 
v___x_160_ = ((size_t)0ULL);
v___x_161_ = lean_usize_of_nat(v___x_158_);
v___x_162_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(v_a_156_, v_as_155_, v___x_160_, v___x_161_);
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1___boxed(lean_object* v_as_163_, lean_object* v_a_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(v_as_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_as_163_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(lean_object* v_a_167_, lean_object* v_as_168_, size_t v_sz_169_, size_t v_i_170_, lean_object* v_b_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_a_179_; uint8_t v___x_183_; 
v___x_183_ = lean_usize_dec_lt(v_i_170_, v_sz_169_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v_b_171_);
return v___x_184_;
}
else
{
lean_object* v_a_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_a_185_ = lean_array_uget_borrowed(v_as_168_, v_i_170_);
lean_inc(v_a_185_);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v_a_185_);
v___x_187_ = l_Lean_Meta_SimpTheoremsArray_isErased(v_b_171_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; 
lean_inc_ref(v___y_173_);
lean_inc(v_a_185_);
v___x_188_ = l_Lean_FVarId_getDecl___redArg(v_a_185_, v___y_173_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_190_; lean_object* v_ctx_191_; lean_object* v_indexConfig_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_189_);
lean_dec_ref(v___x_188_);
v___x_190_ = lean_st_ref_get(v___y_172_);
v_ctx_191_ = lean_ctor_get(v___x_190_, 2);
lean_inc_ref(v_ctx_191_);
lean_dec(v___x_190_);
v_indexConfig_192_ = lean_ctor_get(v_ctx_191_, 4);
lean_inc_ref(v_indexConfig_192_);
lean_dec_ref(v_ctx_191_);
lean_inc(v_a_189_);
v___x_193_ = l_Lean_LocalDecl_toExpr(v_a_189_);
lean_inc_ref(v___x_193_);
lean_inc_ref(v___x_186_);
v___x_194_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v_b_171_, v___x_186_, v___x_193_, v_indexConfig_192_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_196_; uint8_t v_modified_197_; lean_object* v_mvarId_198_; lean_object* v_entries_199_; lean_object* v_ctx_200_; lean_object* v_simprocs_201_; lean_object* v_usedTheorems_202_; lean_object* v_diag_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_243_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref(v___x_194_);
v___x_196_ = lean_st_ref_take(v___y_172_);
v_modified_197_ = lean_ctor_get_uint8(v___x_196_, sizeof(void*)*6);
v_mvarId_198_ = lean_ctor_get(v___x_196_, 0);
v_entries_199_ = lean_ctor_get(v___x_196_, 1);
v_ctx_200_ = lean_ctor_get(v___x_196_, 2);
v_simprocs_201_ = lean_ctor_get(v___x_196_, 3);
v_usedTheorems_202_ = lean_ctor_get(v___x_196_, 4);
v_diag_203_ = lean_ctor_get(v___x_196_, 5);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_243_ == 0)
{
v___x_205_ = v___x_196_;
v_isShared_206_ = v_isSharedCheck_243_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_diag_203_);
lean_inc(v_usedTheorems_202_);
lean_inc(v_simprocs_201_);
lean_inc(v_ctx_200_);
lean_inc(v_entries_199_);
lean_inc(v_mvarId_198_);
lean_dec(v___x_196_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_243_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
lean_inc(v_a_195_);
v___x_207_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v_ctx_200_, v_a_195_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 2, v___x_207_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_mvarId_198_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_entries_199_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_simprocs_201_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_usedTheorems_202_);
lean_ctor_set(v_reuseFailAlloc_242_, 5, v_diag_203_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, sizeof(void*)*6, v_modified_197_);
v___x_209_ = v_reuseFailAlloc_242_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_st_ref_set(v___y_172_, v___x_209_);
v___x_211_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(v_a_167_, v_a_185_);
if (v___x_211_ == 0)
{
lean_dec_ref(v___x_193_);
lean_dec(v_a_189_);
lean_dec_ref(v___x_186_);
v_a_179_ = v_a_195_;
goto v___jp_178_;
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = l_Lean_LocalDecl_type(v_a_189_);
v___x_213_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(v___x_212_, v___y_174_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v_modified_218_; lean_object* v_mvarId_219_; lean_object* v_entries_220_; lean_object* v_ctx_221_; lean_object* v_simprocs_222_; lean_object* v_usedTheorems_223_; lean_object* v_diag_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_233_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref(v___x_213_);
v___x_215_ = l_Lean_LocalDecl_userName(v_a_189_);
lean_dec(v_a_189_);
lean_inc(v_a_214_);
lean_inc(v_a_185_);
v___x_216_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_216_, 0, v_a_185_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
lean_ctor_set(v___x_216_, 2, v___x_186_);
lean_ctor_set(v___x_216_, 3, v_a_214_);
lean_ctor_set(v___x_216_, 4, v_a_214_);
lean_ctor_set(v___x_216_, 5, v___x_193_);
v___x_217_ = lean_st_ref_take(v___y_172_);
v_modified_218_ = lean_ctor_get_uint8(v___x_217_, sizeof(void*)*6);
v_mvarId_219_ = lean_ctor_get(v___x_217_, 0);
v_entries_220_ = lean_ctor_get(v___x_217_, 1);
v_ctx_221_ = lean_ctor_get(v___x_217_, 2);
v_simprocs_222_ = lean_ctor_get(v___x_217_, 3);
v_usedTheorems_223_ = lean_ctor_get(v___x_217_, 4);
v_diag_224_ = lean_ctor_get(v___x_217_, 5);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_233_ == 0)
{
v___x_226_ = v___x_217_;
v_isShared_227_ = v_isSharedCheck_233_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_diag_224_);
lean_inc(v_usedTheorems_223_);
lean_inc(v_simprocs_222_);
lean_inc(v_ctx_221_);
lean_inc(v_entries_220_);
lean_inc(v_mvarId_219_);
lean_dec(v___x_217_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_233_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_array_push(v_entries_220_, v___x_216_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_228_);
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_mvarId_219_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_ctx_221_);
lean_ctor_set(v_reuseFailAlloc_232_, 3, v_simprocs_222_);
lean_ctor_set(v_reuseFailAlloc_232_, 4, v_usedTheorems_223_);
lean_ctor_set(v_reuseFailAlloc_232_, 5, v_diag_224_);
lean_ctor_set_uint8(v_reuseFailAlloc_232_, sizeof(void*)*6, v_modified_218_);
v___x_230_ = v_reuseFailAlloc_232_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; 
v___x_231_ = lean_st_ref_set(v___y_172_, v___x_230_);
v_a_179_ = v_a_195_;
goto v___jp_178_;
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec(v_a_195_);
lean_dec_ref(v___x_193_);
lean_dec(v_a_189_);
lean_dec_ref(v___x_186_);
v_a_234_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_213_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_213_);
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
}
}
else
{
lean_dec_ref(v___x_193_);
lean_dec(v_a_189_);
lean_dec_ref(v___x_186_);
return v___x_194_;
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec_ref(v___x_186_);
lean_dec_ref(v_b_171_);
v_a_244_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_188_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_188_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
else
{
lean_dec_ref(v___x_186_);
v_a_179_ = v_b_171_;
goto v___jp_178_;
}
}
v___jp_178_:
{
size_t v___x_180_; size_t v___x_181_; 
v___x_180_ = ((size_t)1ULL);
v___x_181_ = lean_usize_add(v_i_170_, v___x_180_);
v_i_170_ = v___x_181_;
v_b_171_ = v_a_179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3___boxed(lean_object* v_a_252_, lean_object* v_as_253_, lean_object* v_sz_254_, lean_object* v_i_255_, lean_object* v_b_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
size_t v_sz_boxed_263_; size_t v_i_boxed_264_; lean_object* v_res_265_; 
v_sz_boxed_263_ = lean_unbox_usize(v_sz_254_);
lean_dec(v_sz_254_);
v_i_boxed_264_ = lean_unbox_usize(v_i_255_);
lean_dec(v_i_255_);
v_res_265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(v_a_252_, v_as_253_, v_sz_boxed_263_, v_i_boxed_264_, v_b_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v_as_253_);
lean_dec_ref(v_a_252_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_273_; lean_object* v_mvarId_274_; lean_object* v___f_275_; lean_object* v___x_276_; 
v___x_273_ = lean_st_ref_get(v_a_267_);
v_mvarId_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_mvarId_274_);
lean_dec(v___x_273_);
v___f_275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___closed__0));
v___x_276_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_274_, v___f_275_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_278_; lean_object* v_mvarId_279_; lean_object* v___x_280_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref(v___x_276_);
v___x_278_ = lean_st_ref_get(v_a_267_);
v_mvarId_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_mvarId_279_);
lean_dec(v___x_278_);
v___x_280_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_279_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; lean_object* v_ctx_283_; lean_object* v_simpTheorems_284_; size_t v_sz_285_; size_t v___x_286_; lean_object* v___x_287_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref(v___x_280_);
v___x_282_ = lean_st_ref_get(v_a_267_);
v_ctx_283_ = lean_ctor_get(v___x_282_, 2);
lean_inc_ref(v_ctx_283_);
lean_dec(v___x_282_);
v_simpTheorems_284_ = lean_ctor_get(v_ctx_283_, 5);
lean_inc_ref(v_simpTheorems_284_);
lean_dec_ref(v_ctx_283_);
v_sz_285_ = lean_array_size(v_a_277_);
v___x_286_ = ((size_t)0ULL);
v___x_287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(v_a_281_, v_a_277_, v_sz_285_, v___x_286_, v_simpTheorems_284_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
lean_dec(v_a_277_);
lean_dec(v_a_281_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_295_; 
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v___x_287_, 0);
lean_dec(v_unused_296_);
v___x_289_ = v___x_287_;
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
else
{
lean_dec(v___x_287_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = lean_box(0);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_291_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_a_297_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_287_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_287_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec(v_a_277_);
v_a_305_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_280_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_280_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
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
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_a_313_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_276_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_276_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___boxed(lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg(lean_object* v_a_328_){
_start:
{
lean_object* v___x_330_; lean_object* v_ctx_331_; lean_object* v_simpTheorems_332_; lean_object* v___x_333_; 
v___x_330_ = lean_st_ref_get(v_a_328_);
v_ctx_331_ = lean_ctor_get(v___x_330_, 2);
lean_inc_ref(v_ctx_331_);
lean_dec(v___x_330_);
v_simpTheorems_332_ = lean_ctor_get(v_ctx_331_, 5);
lean_inc_ref(v_simpTheorems_332_);
lean_dec_ref(v_ctx_331_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v_simpTheorems_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg___boxed(lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg(v_a_334_);
lean_dec(v_a_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v___x_343_; lean_object* v_ctx_344_; lean_object* v_simpTheorems_345_; lean_object* v___x_346_; 
v___x_343_ = lean_st_ref_get(v_a_337_);
v_ctx_344_ = lean_ctor_get(v___x_343_, 2);
lean_inc_ref(v_ctx_344_);
lean_dec(v___x_343_);
v_simpTheorems_345_ = lean_ctor_get(v_ctx_344_, 5);
lean_inc_ref(v_simpTheorems_345_);
lean_dec_ref(v_ctx_344_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v_simpTheorems_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___boxed(lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; lean_object* v_ngen_357_; lean_object* v_namePrefix_358_; lean_object* v_idx_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_388_; 
v___x_356_ = lean_st_ref_get(v___y_354_);
v_ngen_357_ = lean_ctor_get(v___x_356_, 2);
lean_inc_ref(v_ngen_357_);
lean_dec(v___x_356_);
v_namePrefix_358_ = lean_ctor_get(v_ngen_357_, 0);
v_idx_359_ = lean_ctor_get(v_ngen_357_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v_ngen_357_);
if (v_isSharedCheck_388_ == 0)
{
v___x_361_ = v_ngen_357_;
v_isShared_362_ = v_isSharedCheck_388_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_idx_359_);
lean_inc(v_namePrefix_358_);
lean_dec(v_ngen_357_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_388_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v_env_364_; lean_object* v_nextMacroScope_365_; lean_object* v_auxDeclNGen_366_; lean_object* v_traceState_367_; lean_object* v_cache_368_; lean_object* v_messages_369_; lean_object* v_infoState_370_; lean_object* v_snapshotTasks_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_386_; 
v___x_363_ = lean_st_ref_take(v___y_354_);
v_env_364_ = lean_ctor_get(v___x_363_, 0);
v_nextMacroScope_365_ = lean_ctor_get(v___x_363_, 1);
v_auxDeclNGen_366_ = lean_ctor_get(v___x_363_, 3);
v_traceState_367_ = lean_ctor_get(v___x_363_, 4);
v_cache_368_ = lean_ctor_get(v___x_363_, 5);
v_messages_369_ = lean_ctor_get(v___x_363_, 6);
v_infoState_370_ = lean_ctor_get(v___x_363_, 7);
v_snapshotTasks_371_ = lean_ctor_get(v___x_363_, 8);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; 
v_unused_387_ = lean_ctor_get(v___x_363_, 2);
lean_dec(v_unused_387_);
v___x_373_ = v___x_363_;
v_isShared_374_ = v_isSharedCheck_386_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_snapshotTasks_371_);
lean_inc(v_infoState_370_);
lean_inc(v_messages_369_);
lean_inc(v_cache_368_);
lean_inc(v_traceState_367_);
lean_inc(v_auxDeclNGen_366_);
lean_inc(v_nextMacroScope_365_);
lean_inc(v_env_364_);
lean_dec(v___x_363_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_386_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_r_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
lean_inc(v_idx_359_);
lean_inc(v_namePrefix_358_);
v_r_375_ = l_Lean_Name_num___override(v_namePrefix_358_, v_idx_359_);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_add(v_idx_359_, v___x_376_);
lean_dec(v_idx_359_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v___x_377_);
v___x_379_ = v___x_361_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_namePrefix_358_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_377_);
v___x_379_ = v_reuseFailAlloc_385_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_381_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 2, v___x_379_);
v___x_381_ = v___x_373_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_env_364_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_nextMacroScope_365_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_384_, 3, v_auxDeclNGen_366_);
lean_ctor_set(v_reuseFailAlloc_384_, 4, v_traceState_367_);
lean_ctor_set(v_reuseFailAlloc_384_, 5, v_cache_368_);
lean_ctor_set(v_reuseFailAlloc_384_, 6, v_messages_369_);
lean_ctor_set(v_reuseFailAlloc_384_, 7, v_infoState_370_);
lean_ctor_set(v_reuseFailAlloc_384_, 8, v_snapshotTasks_371_);
v___x_381_ = v_reuseFailAlloc_384_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_st_ref_set(v___y_354_, v___x_381_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v_r_375_);
return v___x_383_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg___boxed(lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_389_);
lean_dec(v___y_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0(lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_396_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___boxed(lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0(v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(lean_object* v_cls_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_options_412_; uint8_t v_hasTrace_413_; 
v_options_412_ = lean_ctor_get(v___y_410_, 2);
v_hasTrace_413_ = lean_ctor_get_uint8(v_options_412_, sizeof(void*)*1);
if (v_hasTrace_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec(v_cls_409_);
v___x_414_ = lean_box(v_hasTrace_413_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
else
{
lean_object* v_inheritedTraceOptions_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_inheritedTraceOptions_416_ = lean_ctor_get(v___y_410_, 13);
v___x_417_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1));
v___x_418_ = l_Lean_Name_append(v___x_417_, v_cls_409_);
v___x_419_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_416_, v_options_412_, v___x_418_);
lean_dec(v___x_418_);
v___x_420_ = lean_box(v___x_419_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___boxed(lean_object* v_cls_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_cls_422_, v___y_423_);
lean_dec_ref(v___y_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1(lean_object* v_cls_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_cls_426_, v___y_430_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___boxed(lean_object* v_cls_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1(v_cls_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
return v_res_441_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0));
v___x_444_ = l_Lean_stringToMessageData(v___x_443_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2));
v___x_447_ = l_Lean_stringToMessageData(v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__4));
v___x_450_ = l_Lean_stringToMessageData(v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(lean_object* v_x_451_){
_start:
{
switch(lean_obj_tag(v_x_451_))
{
case 0:
{
lean_object* v_declName_453_; uint8_t v_post_454_; uint8_t v_inv_455_; uint8_t v___x_456_; lean_object* v_r_457_; 
v_declName_453_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_declName_453_);
v_post_454_ = lean_ctor_get_uint8(v_x_451_, sizeof(void*)*1);
v_inv_455_ = lean_ctor_get_uint8(v_x_451_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_451_);
v___x_456_ = 0;
v_r_457_ = l_Lean_MessageData_ofConstName(v_declName_453_, v___x_456_);
if (v_post_454_ == 0)
{
if (v_inv_455_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_r_457_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__3, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__3_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__3);
v___x_462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v_r_457_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
else
{
if (v_inv_455_ == 0)
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_r_457_);
return v___x_464_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__5, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__5_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__5);
v___x_466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v_r_457_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
}
case 1:
{
lean_object* v_fvarId_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_477_; 
v_fvarId_468_ = lean_ctor_get(v_x_451_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_x_451_);
if (v_isSharedCheck_477_ == 0)
{
v___x_470_ = v_x_451_;
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_fvarId_468_);
lean_dec(v_x_451_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_472_ = l_Lean_mkFVar(v_fvarId_468_);
v___x_473_ = l_Lean_MessageData_ofExpr(v___x_472_);
if (v_isShared_471_ == 0)
{
lean_ctor_set_tag(v___x_470_, 0);
lean_ctor_set(v___x_470_, 0, v___x_473_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
case 2:
{
lean_object* v_ref_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_ref_478_ = lean_ctor_get(v_x_451_, 1);
lean_inc(v_ref_478_);
lean_dec_ref(v_x_451_);
v___x_479_ = l_Lean_MessageData_ofSyntax(v_ref_478_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
default: 
{
lean_object* v_name_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_489_; 
v_name_481_ = lean_ctor_get(v_x_451_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v_x_451_);
if (v_isSharedCheck_489_ == 0)
{
v___x_483_ = v_x_451_;
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_name_481_);
lean_dec(v_x_451_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = l_Lean_MessageData_ofName(v_name_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 0);
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___boxed(lean_object* v_x_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_x_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(lean_object* v_x_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_x_493_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___boxed(lean_object* v_x_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(v_x_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3_spec__3(lean_object* v_msgData_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; lean_object* v_env_516_; lean_object* v___x_517_; lean_object* v_mctx_518_; lean_object* v_lctx_519_; lean_object* v_options_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_515_ = lean_st_ref_get(v___y_513_);
v_env_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc_ref(v_env_516_);
lean_dec(v___x_515_);
v___x_517_ = lean_st_ref_get(v___y_511_);
v_mctx_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc_ref(v_mctx_518_);
lean_dec(v___x_517_);
v_lctx_519_ = lean_ctor_get(v___y_510_, 2);
v_options_520_ = lean_ctor_get(v___y_512_, 2);
lean_inc_ref(v_options_520_);
lean_inc_ref(v_lctx_519_);
v___x_521_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_521_, 0, v_env_516_);
lean_ctor_set(v___x_521_, 1, v_mctx_518_);
lean_ctor_set(v___x_521_, 2, v_lctx_519_);
lean_ctor_set(v___x_521_, 3, v_options_520_);
v___x_522_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v_msgData_509_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3_spec__3___boxed(lean_object* v_msgData_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3_spec__3(v_msgData_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_530_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_531_; double v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_float_of_nat(v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(lean_object* v_cls_536_, lean_object* v_msg_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_ref_543_; lean_object* v___x_544_; lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_589_; 
v_ref_543_ = lean_ctor_get(v___y_540_, 5);
v___x_544_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3_spec__3(v_msg_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_589_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_589_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_589_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v_traceState_550_; lean_object* v_env_551_; lean_object* v_nextMacroScope_552_; lean_object* v_ngen_553_; lean_object* v_auxDeclNGen_554_; lean_object* v_cache_555_; lean_object* v_messages_556_; lean_object* v_infoState_557_; lean_object* v_snapshotTasks_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_588_; 
v___x_549_ = lean_st_ref_take(v___y_541_);
v_traceState_550_ = lean_ctor_get(v___x_549_, 4);
v_env_551_ = lean_ctor_get(v___x_549_, 0);
v_nextMacroScope_552_ = lean_ctor_get(v___x_549_, 1);
v_ngen_553_ = lean_ctor_get(v___x_549_, 2);
v_auxDeclNGen_554_ = lean_ctor_get(v___x_549_, 3);
v_cache_555_ = lean_ctor_get(v___x_549_, 5);
v_messages_556_ = lean_ctor_get(v___x_549_, 6);
v_infoState_557_ = lean_ctor_get(v___x_549_, 7);
v_snapshotTasks_558_ = lean_ctor_get(v___x_549_, 8);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_588_ == 0)
{
v___x_560_ = v___x_549_;
v_isShared_561_ = v_isSharedCheck_588_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_snapshotTasks_558_);
lean_inc(v_infoState_557_);
lean_inc(v_messages_556_);
lean_inc(v_cache_555_);
lean_inc(v_traceState_550_);
lean_inc(v_auxDeclNGen_554_);
lean_inc(v_ngen_553_);
lean_inc(v_nextMacroScope_552_);
lean_inc(v_env_551_);
lean_dec(v___x_549_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_588_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
uint64_t v_tid_562_; lean_object* v_traces_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_587_; 
v_tid_562_ = lean_ctor_get_uint64(v_traceState_550_, sizeof(void*)*1);
v_traces_563_ = lean_ctor_get(v_traceState_550_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v_traceState_550_);
if (v_isSharedCheck_587_ == 0)
{
v___x_565_ = v_traceState_550_;
v_isShared_566_ = v_isSharedCheck_587_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_traces_563_);
lean_dec(v_traceState_550_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_587_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; double v___x_568_; uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_567_ = lean_box(0);
v___x_568_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0);
v___x_569_ = 0;
v___x_570_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1));
v___x_571_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_571_, 0, v_cls_536_);
lean_ctor_set(v___x_571_, 1, v___x_567_);
lean_ctor_set(v___x_571_, 2, v___x_570_);
lean_ctor_set_float(v___x_571_, sizeof(void*)*3, v___x_568_);
lean_ctor_set_float(v___x_571_, sizeof(void*)*3 + 8, v___x_568_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*3 + 16, v___x_569_);
v___x_572_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2));
v___x_573_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set(v___x_573_, 1, v_a_545_);
lean_ctor_set(v___x_573_, 2, v___x_572_);
lean_inc(v_ref_543_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_ref_543_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = l_Lean_PersistentArray_push___redArg(v_traces_563_, v___x_574_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_575_);
v___x_577_ = v___x_565_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_575_);
lean_ctor_set_uint64(v_reuseFailAlloc_586_, sizeof(void*)*1, v_tid_562_);
v___x_577_ = v_reuseFailAlloc_586_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 4, v___x_577_);
v___x_579_ = v___x_560_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_env_551_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_nextMacroScope_552_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_ngen_553_);
lean_ctor_set(v_reuseFailAlloc_585_, 3, v_auxDeclNGen_554_);
lean_ctor_set(v_reuseFailAlloc_585_, 4, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_585_, 5, v_cache_555_);
lean_ctor_set(v_reuseFailAlloc_585_, 6, v_messages_556_);
lean_ctor_set(v_reuseFailAlloc_585_, 7, v_infoState_557_);
lean_ctor_set(v_reuseFailAlloc_585_, 8, v_snapshotTasks_558_);
v___x_579_ = v_reuseFailAlloc_585_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_580_ = lean_st_ref_set(v___y_541_, v___x_579_);
v___x_581_ = lean_box(0);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_581_);
v___x_583_ = v___x_547_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___boxed(lean_object* v_cls_590_, lean_object* v_msg_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_cls_590_, v_msg_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___lam__0(lean_object* v_fst_598_, lean_object* v_snd_599_, lean_object* v___x_600_, lean_object* v_fvarId_601_, uint8_t v___x_602_, lean_object* v___x_603_, lean_object* v_a_604_, lean_object* v___x_605_, lean_object* v_userName_606_, lean_object* v_origType_607_, lean_object* v_____r_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_st_ref_get(v___y_609_);
v___x_616_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_613_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_618_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref(v___x_616_);
lean_inc_ref(v_snd_599_);
lean_inc_ref(v_fst_598_);
v___x_618_ = l_Lean_Meta_mkExpectedTypeHint(v_fst_598_, v_snd_599_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_ctx_619_; lean_object* v_a_620_; lean_object* v_simpTheorems_621_; lean_object* v_indexConfig_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_ctx_619_ = lean_ctor_get(v___x_615_, 2);
lean_inc_ref(v_ctx_619_);
lean_dec(v___x_615_);
v_a_620_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_620_);
lean_dec_ref(v___x_618_);
v_simpTheorems_621_ = lean_ctor_get(v_ctx_619_, 5);
lean_inc_ref(v_simpTheorems_621_);
lean_dec_ref(v_ctx_619_);
v_indexConfig_622_ = lean_ctor_get(v___x_600_, 4);
lean_inc(v_fvarId_601_);
v___x_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_623_, 0, v_fvarId_601_);
v___x_624_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(v_simpTheorems_621_, v___x_623_);
v___x_625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_625_, 0, v_a_617_);
lean_inc_ref(v_indexConfig_622_);
lean_inc_ref(v___x_625_);
v___x_626_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v___x_624_, v___x_625_, v_a_620_, v_indexConfig_622_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_658_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_658_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_658_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_658_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v_mvarId_632_; lean_object* v_entries_633_; lean_object* v_simprocs_634_; lean_object* v_usedTheorems_635_; lean_object* v_diag_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_656_; 
v___x_631_ = lean_st_ref_take(v___y_609_);
v_mvarId_632_ = lean_ctor_get(v___x_631_, 0);
v_entries_633_ = lean_ctor_get(v___x_631_, 1);
v_simprocs_634_ = lean_ctor_get(v___x_631_, 3);
v_usedTheorems_635_ = lean_ctor_get(v___x_631_, 4);
v_diag_636_ = lean_ctor_get(v___x_631_, 5);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v___x_631_, 2);
lean_dec(v_unused_657_);
v___x_638_ = v___x_631_;
v_isShared_639_ = v_isSharedCheck_656_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_diag_636_);
lean_inc(v_usedTheorems_635_);
lean_inc(v_simprocs_634_);
lean_inc(v_entries_633_);
lean_inc(v_mvarId_632_);
lean_dec(v___x_631_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_656_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___y_641_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = lean_array_get_size(v_entries_633_);
v___x_652_ = lean_nat_dec_lt(v_a_604_, v___x_651_);
if (v___x_652_ == 0)
{
lean_dec_ref(v___x_625_);
lean_dec_ref(v_origType_607_);
lean_dec(v_userName_606_);
lean_dec(v_fvarId_601_);
lean_dec_ref(v_snd_599_);
lean_dec_ref(v_fst_598_);
v___y_641_ = v_entries_633_;
goto v___jp_640_;
}
else
{
lean_object* v_xs_x27_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_xs_x27_653_ = lean_array_fset(v_entries_633_, v_a_604_, v___x_605_);
v___x_654_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_654_, 0, v_fvarId_601_);
lean_ctor_set(v___x_654_, 1, v_userName_606_);
lean_ctor_set(v___x_654_, 2, v___x_625_);
lean_ctor_set(v___x_654_, 3, v_origType_607_);
lean_ctor_set(v___x_654_, 4, v_snd_599_);
lean_ctor_set(v___x_654_, 5, v_fst_598_);
v___x_655_ = lean_array_fset(v_xs_x27_653_, v_a_604_, v___x_654_);
v___y_641_ = v___x_655_;
goto v___jp_640_;
}
v___jp_640_:
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v___x_600_, v_a_627_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 2, v___x_642_);
lean_ctor_set(v___x_638_, 1, v___y_641_);
v___x_644_ = v___x_638_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_mvarId_632_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___y_641_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_simprocs_634_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_usedTheorems_635_);
lean_ctor_set(v_reuseFailAlloc_650_, 5, v_diag_636_);
v___x_644_ = v_reuseFailAlloc_650_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
lean_ctor_set_uint8(v___x_644_, sizeof(void*)*6, v___x_602_);
v___x_645_ = lean_st_ref_set(v___y_609_, v___x_644_);
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_603_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_646_);
v___x_648_ = v___x_629_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec_ref(v___x_625_);
lean_dec_ref(v_origType_607_);
lean_dec(v_userName_606_);
lean_dec_ref(v___x_603_);
lean_dec(v_fvarId_601_);
lean_dec_ref(v___x_600_);
lean_dec_ref(v_snd_599_);
lean_dec_ref(v_fst_598_);
v_a_659_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_626_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_626_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec(v_a_617_);
lean_dec(v___x_615_);
lean_dec_ref(v_origType_607_);
lean_dec(v_userName_606_);
lean_dec_ref(v___x_603_);
lean_dec(v_fvarId_601_);
lean_dec_ref(v___x_600_);
lean_dec_ref(v_snd_599_);
lean_dec_ref(v_fst_598_);
v_a_667_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_618_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_618_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec(v___x_615_);
lean_dec_ref(v_origType_607_);
lean_dec(v_userName_606_);
lean_dec_ref(v___x_603_);
lean_dec(v_fvarId_601_);
lean_dec_ref(v___x_600_);
lean_dec_ref(v_snd_599_);
lean_dec_ref(v_fst_598_);
v_a_675_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_616_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_616_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_fst_683_ = _args[0];
lean_object* v_snd_684_ = _args[1];
lean_object* v___x_685_ = _args[2];
lean_object* v_fvarId_686_ = _args[3];
lean_object* v___x_687_ = _args[4];
lean_object* v___x_688_ = _args[5];
lean_object* v_a_689_ = _args[6];
lean_object* v___x_690_ = _args[7];
lean_object* v_userName_691_ = _args[8];
lean_object* v_origType_692_ = _args[9];
lean_object* v_____r_693_ = _args[10];
lean_object* v___y_694_ = _args[11];
lean_object* v___y_695_ = _args[12];
lean_object* v___y_696_ = _args[13];
lean_object* v___y_697_ = _args[14];
lean_object* v___y_698_ = _args[15];
lean_object* v___y_699_ = _args[16];
_start:
{
uint8_t v___x_27113__boxed_700_; lean_object* v_res_701_; 
v___x_27113__boxed_700_ = lean_unbox(v___x_687_);
v_res_701_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___lam__0(v_fst_683_, v_snd_684_, v___x_685_, v_fvarId_686_, v___x_27113__boxed_700_, v___x_688_, v_a_689_, v___x_690_, v_userName_691_, v_origType_692_, v_____r_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec(v_a_689_);
return v_res_701_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__6));
v___x_716_ = l_Lean_stringToMessageData(v___x_715_);
return v___x_716_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__8));
v___x_719_ = l_Lean_stringToMessageData(v___x_718_);
return v___x_719_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__10));
v___x_722_ = l_Lean_stringToMessageData(v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg(lean_object* v_upperBound_723_, lean_object* v___x_724_, lean_object* v___x_725_, lean_object* v_a_726_, lean_object* v_b_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_a_735_; lean_object* v___y_740_; uint8_t v___x_759_; 
v___x_759_ = lean_nat_dec_lt(v_a_726_, v_upperBound_723_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; 
lean_dec(v_a_726_);
lean_dec_ref(v___x_725_);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v_b_727_);
return v___x_760_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v_ctx_765_; lean_object* v_ctx_766_; lean_object* v_simpTheorems_767_; lean_object* v___x_768_; lean_object* v_fvarId_769_; lean_object* v_userName_770_; lean_object* v_id_771_; lean_object* v_origType_772_; lean_object* v_type_773_; lean_object* v_proof_774_; lean_object* v_mvarId_775_; lean_object* v_usedTheorems_776_; lean_object* v_diag_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec_ref(v_b_727_);
v___x_761_ = lean_st_ref_get(v___y_728_);
v___x_762_ = lean_st_ref_get(v___y_728_);
v___x_763_ = lean_st_ref_get(v___y_728_);
v___x_764_ = lean_st_ref_get(v___y_728_);
v_ctx_765_ = lean_ctor_get(v___x_762_, 2);
lean_inc_ref(v_ctx_765_);
lean_dec(v___x_762_);
v_ctx_766_ = lean_ctor_get(v___x_761_, 2);
lean_inc_ref(v_ctx_766_);
lean_dec(v___x_761_);
v_simpTheorems_767_ = lean_ctor_get(v_ctx_765_, 5);
lean_inc_ref(v_simpTheorems_767_);
lean_dec_ref(v_ctx_765_);
v___x_768_ = lean_array_fget_borrowed(v___x_724_, v_a_726_);
v_fvarId_769_ = lean_ctor_get(v___x_768_, 0);
v_userName_770_ = lean_ctor_get(v___x_768_, 1);
v_id_771_ = lean_ctor_get(v___x_768_, 2);
v_origType_772_ = lean_ctor_get(v___x_768_, 3);
v_type_773_ = lean_ctor_get(v___x_768_, 4);
v_proof_774_ = lean_ctor_get(v___x_768_, 5);
v_mvarId_775_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_mvarId_775_);
lean_dec(v___x_763_);
v_usedTheorems_776_ = lean_ctor_get(v___x_764_, 4);
lean_inc_ref(v_usedTheorems_776_);
v_diag_777_ = lean_ctor_get(v___x_764_, 5);
lean_inc_ref(v_diag_777_);
lean_dec(v___x_764_);
lean_inc_ref(v_id_771_);
v___x_778_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(v_simpTheorems_767_, v_id_771_);
v___x_779_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v_ctx_766_, v___x_778_);
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v_usedTheorems_776_);
lean_ctor_set(v___x_781_, 1, v_diag_777_);
lean_inc_ref(v___x_725_);
lean_inc_ref(v___x_779_);
lean_inc_ref(v_type_773_);
lean_inc_ref(v_proof_774_);
v___x_782_ = l_Lean_Meta_simpStep(v_mvarId_775_, v_proof_774_, v_type_773_, v___x_779_, v___x_725_, v___x_780_, v___x_759_, v___x_781_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec_ref(v___x_781_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_881_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_881_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_881_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_881_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_fst_787_; lean_object* v_snd_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_880_; 
v_fst_787_ = lean_ctor_get(v_a_783_, 0);
v_snd_788_ = lean_ctor_get(v_a_783_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v_a_783_);
if (v_isSharedCheck_880_ == 0)
{
v___x_790_ = v_a_783_;
v_isShared_791_ = v_isSharedCheck_880_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_snd_788_);
lean_inc(v_fst_787_);
lean_dec(v_a_783_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_880_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; uint8_t v_modified_793_; lean_object* v_mvarId_794_; lean_object* v_entries_795_; lean_object* v_ctx_796_; lean_object* v_simprocs_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_877_; 
v___x_792_ = lean_st_ref_take(v___y_728_);
v_modified_793_ = lean_ctor_get_uint8(v___x_792_, sizeof(void*)*6);
v_mvarId_794_ = lean_ctor_get(v___x_792_, 0);
v_entries_795_ = lean_ctor_get(v___x_792_, 1);
v_ctx_796_ = lean_ctor_get(v___x_792_, 2);
v_simprocs_797_ = lean_ctor_get(v___x_792_, 3);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; lean_object* v_unused_879_; 
v_unused_878_ = lean_ctor_get(v___x_792_, 5);
lean_dec(v_unused_878_);
v_unused_879_ = lean_ctor_get(v___x_792_, 4);
lean_dec(v_unused_879_);
v___x_799_ = v___x_792_;
v_isShared_800_ = v_isSharedCheck_877_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_simprocs_797_);
lean_inc(v_ctx_796_);
lean_inc(v_entries_795_);
lean_inc(v_mvarId_794_);
lean_dec(v___x_792_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_877_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_usedTheorems_801_; lean_object* v_diag_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_876_; 
v_usedTheorems_801_ = lean_ctor_get(v_snd_788_, 0);
v_diag_802_ = lean_ctor_get(v_snd_788_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v_snd_788_);
if (v_isSharedCheck_876_ == 0)
{
v___x_804_ = v_snd_788_;
v_isShared_805_ = v_isSharedCheck_876_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_diag_802_);
lean_inc(v_usedTheorems_801_);
lean_dec(v_snd_788_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_876_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 5, v_diag_802_);
lean_ctor_set(v___x_799_, 4, v_usedTheorems_801_);
v___x_807_ = v___x_799_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_mvarId_794_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_entries_795_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_ctx_796_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v_simprocs_797_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v_usedTheorems_801_);
lean_ctor_set(v_reuseFailAlloc_875_, 5, v_diag_802_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*6, v_modified_793_);
v___x_807_ = v_reuseFailAlloc_875_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_st_ref_set(v___y_728_, v___x_807_);
v___x_809_ = lean_box(0);
if (lean_obj_tag(v_fst_787_) == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
lean_del_object(v___x_804_);
lean_dec_ref(v___x_779_);
lean_dec(v_a_726_);
lean_dec_ref(v___x_725_);
v___x_810_ = lean_box(v___x_759_);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 1, v___x_809_);
lean_ctor_set(v___x_790_, 0, v___x_811_);
v___x_813_ = v___x_790_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_809_);
v___x_813_ = v_reuseFailAlloc_817_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_815_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_813_);
v___x_815_ = v___x_785_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
lean_object* v_val_818_; lean_object* v_fst_819_; lean_object* v_snd_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_874_; 
lean_del_object(v___x_790_);
lean_del_object(v___x_785_);
v_val_818_ = lean_ctor_get(v_fst_787_, 0);
lean_inc(v_val_818_);
lean_dec_ref(v_fst_787_);
v_fst_819_ = lean_ctor_get(v_val_818_, 0);
v_snd_820_ = lean_ctor_get(v_val_818_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v_val_818_);
if (v_isSharedCheck_874_ == 0)
{
v___x_822_ = v_val_818_;
v_isShared_823_ = v_isSharedCheck_874_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_snd_820_);
lean_inc(v_fst_819_);
lean_dec(v_val_818_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_874_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__0));
v___x_825_ = lean_expr_eqv(v_snd_820_, v_type_773_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__5));
v___x_827_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v___x_826_, v___y_731_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; uint8_t v___x_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref(v___x_827_);
v___x_829_ = lean_unbox(v_a_828_);
lean_dec(v_a_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
lean_del_object(v___x_822_);
lean_del_object(v___x_804_);
lean_inc_ref(v_origType_772_);
lean_inc(v_userName_770_);
lean_inc(v_fvarId_769_);
v___x_830_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___lam__0(v_fst_819_, v_snd_820_, v___x_779_, v_fvarId_769_, v___x_759_, v___x_824_, v_a_726_, v___x_809_, v_userName_770_, v_origType_772_, v___x_809_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
v___y_740_ = v___x_830_;
goto v___jp_739_;
}
else
{
lean_object* v___x_831_; 
lean_inc_ref(v_id_771_);
v___x_831_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_id_771_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref(v___x_831_);
v___x_833_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__7);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 7);
lean_ctor_set(v___x_822_, 1, v_a_832_);
lean_ctor_set(v___x_822_, 0, v___x_833_);
v___x_835_ = v___x_822_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_a_832_);
v___x_835_ = v_reuseFailAlloc_857_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__9);
if (v_isShared_805_ == 0)
{
lean_ctor_set_tag(v___x_804_, 7);
lean_ctor_set(v___x_804_, 1, v___x_836_);
lean_ctor_set(v___x_804_, 0, v___x_835_);
v___x_838_ = v___x_804_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_836_);
v___x_838_ = v_reuseFailAlloc_856_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_inc_ref(v_type_773_);
v___x_839_ = l_Lean_MessageData_ofExpr(v_type_773_);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__11);
v___x_842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
lean_inc(v_snd_820_);
v___x_843_ = l_Lean_MessageData_ofExpr(v_snd_820_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v___x_826_, v___x_844_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v___x_845_);
lean_inc_ref(v_origType_772_);
lean_inc(v_userName_770_);
lean_inc(v_fvarId_769_);
v___x_847_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___lam__0(v_fst_819_, v_snd_820_, v___x_779_, v_fvarId_769_, v___x_759_, v___x_824_, v_a_726_, v___x_809_, v_userName_770_, v_origType_772_, v_a_846_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
v___y_740_ = v___x_847_;
goto v___jp_739_;
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_snd_820_);
lean_dec(v_fst_819_);
lean_dec_ref(v___x_779_);
lean_dec(v_a_726_);
lean_dec_ref(v___x_725_);
v_a_848_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_845_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_845_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_del_object(v___x_822_);
lean_dec(v_snd_820_);
lean_dec(v_fst_819_);
lean_del_object(v___x_804_);
lean_dec_ref(v___x_779_);
lean_dec(v_a_726_);
lean_dec_ref(v___x_725_);
v_a_858_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_831_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_831_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_del_object(v___x_822_);
lean_dec(v_snd_820_);
lean_dec(v_fst_819_);
lean_del_object(v___x_804_);
lean_dec_ref(v___x_779_);
lean_dec(v_a_726_);
lean_dec_ref(v___x_725_);
v_a_866_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_827_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_827_);
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
else
{
lean_del_object(v___x_822_);
lean_dec(v_snd_820_);
lean_dec(v_fst_819_);
lean_del_object(v___x_804_);
lean_dec_ref(v___x_779_);
v_a_735_ = v___x_824_;
goto v___jp_734_;
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
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec_ref(v___x_779_);
lean_dec(v_a_726_);
lean_dec_ref(v___x_725_);
v_a_882_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_782_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_782_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
v___jp_734_:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_nat_add(v_a_726_, v___x_736_);
lean_dec(v_a_726_);
v_a_726_ = v___x_737_;
v_b_727_ = v_a_735_;
goto _start;
}
v___jp_739_:
{
if (lean_obj_tag(v___y_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_750_; 
v_a_741_ = lean_ctor_get(v___y_740_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___y_740_);
if (v_isSharedCheck_750_ == 0)
{
v___x_743_ = v___y_740_;
v_isShared_744_ = v_isSharedCheck_750_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___y_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_750_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
if (lean_obj_tag(v_a_741_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; 
lean_dec(v_a_726_);
lean_dec_ref(v___x_725_);
v_a_745_ = lean_ctor_get(v_a_741_, 0);
lean_inc(v_a_745_);
lean_dec_ref(v_a_741_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v_a_745_);
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
else
{
lean_object* v_a_749_; 
lean_del_object(v___x_743_);
v_a_749_ = lean_ctor_get(v_a_741_, 0);
lean_inc(v_a_749_);
lean_dec_ref(v_a_741_);
v_a_735_ = v_a_749_;
goto v___jp_734_;
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v_a_726_);
lean_dec_ref(v___x_725_);
v_a_751_ = lean_ctor_get(v___y_740_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___y_740_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___y_740_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___y_740_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___boxed(lean_object* v_upperBound_890_, lean_object* v___x_891_, lean_object* v___x_892_, lean_object* v_a_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg(v_upperBound_890_, v___x_891_, v___x_892_, v_a_893_, v_b_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___x_891_);
lean_dec(v_upperBound_890_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___x_922_; lean_object* v_mvarId_923_; lean_object* v_entries_924_; lean_object* v_ctx_925_; lean_object* v_simprocs_926_; lean_object* v_usedTheorems_927_; lean_object* v_diag_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_1035_; 
v___x_922_ = lean_st_ref_take(v_a_905_);
v_mvarId_923_ = lean_ctor_get(v___x_922_, 0);
v_entries_924_ = lean_ctor_get(v___x_922_, 1);
v_ctx_925_ = lean_ctor_get(v___x_922_, 2);
v_simprocs_926_ = lean_ctor_get(v___x_922_, 3);
v_usedTheorems_927_ = lean_ctor_get(v___x_922_, 4);
v_diag_928_ = lean_ctor_get(v___x_922_, 5);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_930_ = v___x_922_;
v_isShared_931_ = v_isSharedCheck_1035_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_diag_928_);
lean_inc(v_usedTheorems_927_);
lean_inc(v_simprocs_926_);
lean_inc(v_ctx_925_);
lean_inc(v_entries_924_);
lean_inc(v_mvarId_923_);
lean_dec(v___x_922_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_1035_;
goto v_resetjp_929_;
}
v___jp_911_:
{
lean_object* v___x_917_; uint8_t v_modified_918_; 
v___x_917_ = lean_st_ref_get(v___y_912_);
v_modified_918_ = lean_ctor_get_uint8(v___x_917_, sizeof(void*)*6);
lean_dec(v___x_917_);
if (v_modified_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_box(v_modified_918_);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
else
{
v_a_905_ = v___y_912_;
v_a_906_ = v___y_913_;
v_a_907_ = v___y_914_;
v_a_908_ = v___y_915_;
v_a_909_ = v___y_916_;
goto _start;
}
}
v_resetjp_929_:
{
uint8_t v___x_932_; lean_object* v___x_934_; 
v___x_932_ = 0;
if (v_isShared_931_ == 0)
{
v___x_934_ = v___x_930_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_mvarId_923_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_entries_924_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_ctx_925_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v_simprocs_926_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v_usedTheorems_927_);
lean_ctor_set(v_reuseFailAlloc_1034_, 5, v_diag_928_);
v___x_934_ = v_reuseFailAlloc_1034_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v_entries_938_; lean_object* v_simprocs_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*6, v___x_932_);
v___x_935_ = lean_st_ref_set(v_a_905_, v___x_934_);
v___x_936_ = lean_st_ref_get(v_a_905_);
v___x_937_ = lean_st_ref_get(v_a_905_);
v_entries_938_ = lean_ctor_get(v___x_937_, 1);
lean_inc_ref(v_entries_938_);
lean_dec(v___x_937_);
v_simprocs_939_ = lean_ctor_get(v___x_936_, 3);
lean_inc_ref(v_simprocs_939_);
lean_dec(v___x_936_);
v___x_940_ = lean_array_get_size(v_entries_938_);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_box(0);
v___x_943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__0));
lean_inc_ref(v_simprocs_939_);
v___x_944_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg(v___x_940_, v_entries_938_, v_simprocs_939_, v___x_941_, v___x_943_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
lean_dec_ref(v_entries_938_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_1025_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_1025_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_1025_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_fst_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_1023_; 
v_fst_949_ = lean_ctor_get(v_a_945_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_a_945_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; 
v_unused_1024_ = lean_ctor_get(v_a_945_, 1);
lean_dec(v_unused_1024_);
v___x_951_ = v_a_945_;
v_isShared_952_ = v_isSharedCheck_1023_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_fst_949_);
lean_dec(v_a_945_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_1023_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
if (lean_obj_tag(v_fst_949_) == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_mvarId_956_; lean_object* v_ctx_957_; lean_object* v_usedTheorems_958_; lean_object* v_diag_959_; uint8_t v___x_960_; lean_object* v___x_962_; 
lean_del_object(v___x_947_);
v___x_953_ = lean_st_ref_get(v_a_905_);
v___x_954_ = lean_st_ref_get(v_a_905_);
v___x_955_ = lean_st_ref_get(v_a_905_);
v_mvarId_956_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_mvarId_956_);
lean_dec(v___x_953_);
v_ctx_957_ = lean_ctor_get(v___x_954_, 2);
lean_inc_ref(v_ctx_957_);
lean_dec(v___x_954_);
v_usedTheorems_958_ = lean_ctor_get(v___x_955_, 4);
lean_inc_ref(v_usedTheorems_958_);
v_diag_959_ = lean_ctor_get(v___x_955_, 5);
lean_inc_ref(v_diag_959_);
lean_dec(v___x_955_);
v___x_960_ = 1;
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v_diag_959_);
lean_ctor_set(v___x_951_, 0, v_usedTheorems_958_);
v___x_962_ = v___x_951_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_usedTheorems_958_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_diag_959_);
v___x_962_ = v_reuseFailAlloc_1018_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; 
lean_inc(v_mvarId_956_);
v___x_963_ = l_Lean_Meta_simpTarget(v_mvarId_956_, v_ctx_957_, v_simprocs_939_, v___x_942_, v___x_960_, v___x_962_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1009_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_1009_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1009_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_fst_968_; lean_object* v_snd_969_; lean_object* v___x_970_; uint8_t v_modified_971_; lean_object* v_mvarId_972_; lean_object* v_entries_973_; lean_object* v_ctx_974_; lean_object* v_simprocs_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1006_; 
v_fst_968_ = lean_ctor_get(v_a_964_, 0);
lean_inc(v_fst_968_);
v_snd_969_ = lean_ctor_get(v_a_964_, 1);
lean_inc(v_snd_969_);
lean_dec(v_a_964_);
v___x_970_ = lean_st_ref_take(v_a_905_);
v_modified_971_ = lean_ctor_get_uint8(v___x_970_, sizeof(void*)*6);
v_mvarId_972_ = lean_ctor_get(v___x_970_, 0);
v_entries_973_ = lean_ctor_get(v___x_970_, 1);
v_ctx_974_ = lean_ctor_get(v___x_970_, 2);
v_simprocs_975_ = lean_ctor_get(v___x_970_, 3);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; lean_object* v_unused_1008_; 
v_unused_1007_ = lean_ctor_get(v___x_970_, 5);
lean_dec(v_unused_1007_);
v_unused_1008_ = lean_ctor_get(v___x_970_, 4);
lean_dec(v_unused_1008_);
v___x_977_ = v___x_970_;
v_isShared_978_ = v_isSharedCheck_1006_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_simprocs_975_);
lean_inc(v_ctx_974_);
lean_inc(v_entries_973_);
lean_inc(v_mvarId_972_);
lean_dec(v___x_970_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1006_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_usedTheorems_979_; lean_object* v_diag_980_; lean_object* v___x_982_; 
v_usedTheorems_979_ = lean_ctor_get(v_snd_969_, 0);
lean_inc_ref(v_usedTheorems_979_);
v_diag_980_ = lean_ctor_get(v_snd_969_, 1);
lean_inc_ref(v_diag_980_);
lean_dec(v_snd_969_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 5, v_diag_980_);
lean_ctor_set(v___x_977_, 4, v_usedTheorems_979_);
v___x_982_ = v___x_977_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_mvarId_972_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_entries_973_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_ctx_974_);
lean_ctor_set(v_reuseFailAlloc_1005_, 3, v_simprocs_975_);
lean_ctor_set(v_reuseFailAlloc_1005_, 4, v_usedTheorems_979_);
lean_ctor_set(v_reuseFailAlloc_1005_, 5, v_diag_980_);
lean_ctor_set_uint8(v_reuseFailAlloc_1005_, sizeof(void*)*6, v_modified_971_);
v___x_982_ = v_reuseFailAlloc_1005_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; 
v___x_983_ = lean_st_ref_set(v_a_905_, v___x_982_);
if (lean_obj_tag(v_fst_968_) == 0)
{
lean_object* v___x_984_; lean_object* v___x_986_; 
lean_dec(v_mvarId_956_);
v___x_984_ = lean_box(v___x_960_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_984_);
v___x_986_ = v___x_966_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
else
{
lean_object* v_val_988_; uint8_t v___x_989_; 
lean_del_object(v___x_966_);
v_val_988_ = lean_ctor_get(v_fst_968_, 0);
lean_inc(v_val_988_);
lean_dec_ref(v_fst_968_);
v___x_989_ = l_Lean_instBEqMVarId_beq(v_mvarId_956_, v_val_988_);
lean_dec(v_mvarId_956_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v_entries_991_; lean_object* v_ctx_992_; lean_object* v_simprocs_993_; lean_object* v_usedTheorems_994_; lean_object* v_diag_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1003_; 
v___x_990_ = lean_st_ref_take(v_a_905_);
v_entries_991_ = lean_ctor_get(v___x_990_, 1);
v_ctx_992_ = lean_ctor_get(v___x_990_, 2);
v_simprocs_993_ = lean_ctor_get(v___x_990_, 3);
v_usedTheorems_994_ = lean_ctor_get(v___x_990_, 4);
v_diag_995_ = lean_ctor_get(v___x_990_, 5);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v___x_990_, 0);
lean_dec(v_unused_1004_);
v___x_997_ = v___x_990_;
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_diag_995_);
lean_inc(v_usedTheorems_994_);
lean_inc(v_simprocs_993_);
lean_inc(v_ctx_992_);
lean_inc(v_entries_991_);
lean_dec(v___x_990_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v_val_988_);
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_val_988_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_entries_991_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_ctx_992_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_simprocs_993_);
lean_ctor_set(v_reuseFailAlloc_1002_, 4, v_usedTheorems_994_);
lean_ctor_set(v_reuseFailAlloc_1002_, 5, v_diag_995_);
v___x_1000_ = v_reuseFailAlloc_1002_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; 
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*6, v___x_960_);
v___x_1001_ = lean_st_ref_set(v_a_905_, v___x_1000_);
v___y_912_ = v_a_905_;
v___y_913_ = v_a_906_;
v___y_914_ = v_a_907_;
v___y_915_ = v_a_908_;
v___y_916_ = v_a_909_;
goto v___jp_911_;
}
}
}
else
{
lean_dec(v_val_988_);
v___y_912_ = v_a_905_;
v___y_913_ = v_a_906_;
v___y_914_ = v_a_907_;
v___y_915_ = v_a_908_;
v___y_916_ = v_a_909_;
goto v___jp_911_;
}
}
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_mvarId_956_);
v_a_1010_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_963_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_963_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
else
{
lean_object* v_val_1019_; lean_object* v___x_1021_; 
lean_del_object(v___x_951_);
lean_dec_ref(v_simprocs_939_);
v_val_1019_ = lean_ctor_get(v_fst_949_, 0);
lean_inc(v_val_1019_);
lean_dec_ref(v_fst_949_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v_val_1019_);
v___x_1021_ = v___x_947_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_val_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec_ref(v_simprocs_939_);
v_a_1026_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_944_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_944_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___boxed(lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(lean_object* v_cls_1043_, lean_object* v_msg_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_cls_1043_, v_msg_1044_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___boxed(lean_object* v_cls_1052_, lean_object* v_msg_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(v_cls_1052_, v_msg_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4(lean_object* v_upperBound_1061_, lean_object* v___x_1062_, lean_object* v___x_1063_, lean_object* v_inst_1064_, lean_object* v_R_1065_, lean_object* v_a_1066_, lean_object* v_b_1067_, lean_object* v_c_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg(v_upperBound_1061_, v___x_1062_, v___x_1063_, v_a_1066_, v_b_1067_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___boxed(lean_object* v_upperBound_1076_, lean_object* v___x_1077_, lean_object* v___x_1078_, lean_object* v_inst_1079_, lean_object* v_R_1080_, lean_object* v_a_1081_, lean_object* v_b_1082_, lean_object* v_c_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4(v_upperBound_1076_, v___x_1077_, v___x_1078_, v_inst_1079_, v_R_1080_, v_a_1081_, v_b_1082_, v_c_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___x_1077_);
lean_dec(v_upperBound_1076_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(lean_object* v_as_1091_, size_t v_sz_1092_, size_t v_i_1093_, lean_object* v_b_1094_){
_start:
{
lean_object* v_a_1097_; uint8_t v___x_1101_; 
v___x_1101_ = lean_usize_dec_lt(v_i_1093_, v_sz_1092_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v_b_1094_);
return v___x_1102_;
}
else
{
lean_object* v_snd_1103_; lean_object* v_fst_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1141_; 
v_snd_1103_ = lean_ctor_get(v_b_1094_, 1);
v_fst_1104_ = lean_ctor_get(v_b_1094_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_b_1094_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1106_ = v_b_1094_;
v_isShared_1107_ = v_isSharedCheck_1141_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_snd_1103_);
lean_inc(v_fst_1104_);
lean_dec(v_b_1094_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1141_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_fst_1108_; lean_object* v_snd_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1140_; 
v_fst_1108_ = lean_ctor_get(v_snd_1103_, 0);
v_snd_1109_ = lean_ctor_get(v_snd_1103_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_snd_1103_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1111_ = v_snd_1103_;
v_isShared_1112_ = v_isSharedCheck_1140_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_snd_1109_);
lean_inc(v_fst_1108_);
lean_dec(v_snd_1103_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1140_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v_a_1113_; lean_object* v_fvarId_1114_; lean_object* v_userName_1115_; lean_object* v_origType_1116_; lean_object* v_type_1117_; lean_object* v_proof_1118_; uint8_t v___x_1132_; 
v_a_1113_ = lean_array_uget_borrowed(v_as_1091_, v_i_1093_);
v_fvarId_1114_ = lean_ctor_get(v_a_1113_, 0);
v_userName_1115_ = lean_ctor_get(v_a_1113_, 1);
v_origType_1116_ = lean_ctor_get(v_a_1113_, 3);
v_type_1117_ = lean_ctor_get(v_a_1113_, 4);
v_proof_1118_ = lean_ctor_get(v_a_1113_, 5);
lean_inc_ref(v_type_1117_);
v___x_1132_ = l_Lean_Expr_isTrue(v_type_1117_);
if (v___x_1132_ == 0)
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_unbox(v_snd_1109_);
if (v___x_1133_ == 0)
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_expr_eqv(v_type_1117_, v_origType_1116_);
if (v___x_1134_ == 0)
{
lean_dec(v_snd_1109_);
goto v___jp_1119_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_del_object(v___x_1111_);
lean_del_object(v___x_1106_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_fst_1108_);
lean_ctor_set(v___x_1135_, 1, v_snd_1109_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v_fst_1104_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v_a_1097_ = v___x_1136_;
goto v___jp_1096_;
}
}
else
{
lean_dec(v_snd_1109_);
goto v___jp_1119_;
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_del_object(v___x_1111_);
lean_del_object(v___x_1106_);
lean_inc(v_fvarId_1114_);
v___x_1137_ = lean_array_push(v_fst_1108_, v_fvarId_1114_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v_snd_1109_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_fst_1104_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v_a_1097_ = v___x_1139_;
goto v___jp_1096_;
}
v___jp_1119_:
{
lean_object* v___x_1120_; uint8_t v___x_1121_; uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
lean_inc(v_fvarId_1114_);
v___x_1120_ = lean_array_push(v_fst_1108_, v_fvarId_1114_);
v___x_1121_ = 0;
v___x_1122_ = 0;
lean_inc_ref(v_proof_1118_);
lean_inc_ref(v_type_1117_);
lean_inc(v_userName_1115_);
v___x_1123_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1123_, 0, v_userName_1115_);
lean_ctor_set(v___x_1123_, 1, v_type_1117_);
lean_ctor_set(v___x_1123_, 2, v_proof_1118_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*3, v___x_1121_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*3 + 1, v___x_1122_);
v___x_1124_ = lean_array_push(v_fst_1104_, v___x_1123_);
v___x_1125_ = lean_box(v___x_1101_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v___x_1125_);
lean_ctor_set(v___x_1111_, 0, v___x_1120_);
v___x_1127_ = v___x_1111_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1129_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 1, v___x_1127_);
lean_ctor_set(v___x_1106_, 0, v___x_1124_);
v___x_1129_ = v___x_1106_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
v_a_1097_ = v___x_1129_;
goto v___jp_1096_;
}
}
}
}
}
}
v___jp_1096_:
{
size_t v___x_1098_; size_t v___x_1099_; 
v___x_1098_ = ((size_t)1ULL);
v___x_1099_ = lean_usize_add(v_i_1093_, v___x_1098_);
v_i_1093_ = v___x_1099_;
v_b_1094_ = v_a_1097_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg___boxed(lean_object* v_as_1142_, lean_object* v_sz_1143_, lean_object* v_i_1144_, lean_object* v_b_1145_, lean_object* v___y_1146_){
_start:
{
size_t v_sz_boxed_1147_; size_t v_i_boxed_1148_; lean_object* v_res_1149_; 
v_sz_boxed_1147_ = lean_unbox_usize(v_sz_1143_);
lean_dec(v_sz_1143_);
v_i_boxed_1148_ = lean_unbox_usize(v_i_1144_);
lean_dec(v_i_1144_);
v_res_1149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_as_1142_, v_sz_boxed_1147_, v_i_boxed_1148_, v_b_1145_);
lean_dec_ref(v_as_1142_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_main(lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v___x_1159_; 
lean_dec_ref(v___x_1158_);
v___x_1159_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1220_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1220_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1220_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_unbox(v_a_1160_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_entries_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; size_t v_sz_1171_; size_t v___x_1172_; lean_object* v___x_1173_; 
lean_del_object(v___x_1162_);
v___x_1165_ = lean_st_ref_get(v_a_1152_);
v___x_1166_ = lean_st_ref_get(v_a_1152_);
v_entries_1167_ = lean_ctor_get(v___x_1166_, 1);
lean_inc_ref(v_entries_1167_);
lean_dec(v___x_1166_);
v___x_1168_ = ((lean_object*)(l_Lean_Meta_SimpAll_main___closed__0));
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v_a_1160_);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v_sz_1171_ = lean_array_size(v_entries_1167_);
v___x_1172_ = ((size_t)0ULL);
v___x_1173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_entries_1167_, v_sz_1171_, v___x_1172_, v___x_1170_);
lean_dec_ref(v_entries_1167_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v_mvarId_1175_; lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v___x_1178_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref(v___x_1173_);
v_mvarId_1175_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_mvarId_1175_);
lean_dec(v___x_1165_);
v_fst_1176_ = lean_ctor_get(v_a_1174_, 0);
lean_inc(v_fst_1176_);
v_snd_1177_ = lean_ctor_get(v_a_1174_, 1);
lean_inc(v_snd_1177_);
lean_dec(v_a_1174_);
v___x_1178_ = l_Lean_MVarId_assertHypotheses(v_mvarId_1175_, v_fst_1176_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v_snd_1180_; lean_object* v_fst_1181_; lean_object* v___x_1182_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref(v___x_1178_);
v_snd_1180_ = lean_ctor_get(v_a_1179_, 1);
lean_inc(v_snd_1180_);
lean_dec(v_a_1179_);
v_fst_1181_ = lean_ctor_get(v_snd_1177_, 0);
lean_inc(v_fst_1181_);
lean_dec(v_snd_1177_);
v___x_1182_ = l_Lean_MVarId_tryClearMany(v_snd_1180_, v_fst_1181_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_fst_1181_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1191_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_a_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1187_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_a_1192_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1182_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1182_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec(v_snd_1177_);
v_a_1200_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1178_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1178_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec(v___x_1165_);
v_a_1208_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1173_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1173_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
lean_dec(v_a_1160_);
v___x_1216_ = lean_box(0);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1216_);
v___x_1218_ = v___x_1162_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
v_a_1221_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1159_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1159_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_a_1229_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1158_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1158_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_main___boxed(lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_Meta_SimpAll_main(v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(lean_object* v_as_1244_, size_t v_sz_1245_, size_t v_i_1246_, lean_object* v_b_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_as_1244_, v_sz_1245_, v_i_1246_, v_b_1247_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___boxed(lean_object* v_as_1255_, lean_object* v_sz_1256_, lean_object* v_i_1257_, lean_object* v_b_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
size_t v_sz_boxed_1265_; size_t v_i_boxed_1266_; lean_object* v_res_1267_; 
v_sz_boxed_1265_ = lean_unbox_usize(v_sz_1256_);
lean_dec(v_sz_1256_);
v_i_boxed_1266_ = lean_unbox_usize(v_i_1257_);
lean_dec(v_i_1257_);
v_res_1267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(v_as_1255_, v_sz_boxed_1265_, v_i_boxed_1266_, v_b_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v_as_1255_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(lean_object* v_mvarId_1268_, lean_object* v_x_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1268_, v_x_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_a_1284_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1275_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1275_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg___boxed(lean_object* v_mvarId_1292_, lean_object* v_x_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1292_, v_x_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(lean_object* v_00_u03b1_1300_, lean_object* v_mvarId_1301_, lean_object* v_x_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1301_, v_x_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___boxed(lean_object* v_00_u03b1_1309_, lean_object* v_mvarId_1310_, lean_object* v_x_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(v_00_u03b1_1309_, v_mvarId_1310_, v_x_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(lean_object* v_msg_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_ref_1324_; lean_object* v___x_1325_; lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1334_; 
v_ref_1324_ = lean_ctor_get(v___y_1321_, 5);
v___x_1325_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3_spec__3(v_msg_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
lean_inc(v_ref_1324_);
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_ref_1324_);
lean_ctor_set(v___x_1330_, 1, v_a_1326_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set_tag(v___x_1328_, 1);
lean_ctor_set(v___x_1328_, 0, v___x_1330_);
v___x_1332_ = v___x_1328_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg___boxed(lean_object* v_msg_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v_msg_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
return v_res_1341_;
}
}
static lean_object* _init_l_Lean_Meta_simpAll___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = ((lean_object*)(l_Lean_Meta_simpAll___lam__0___closed__0));
v___x_1344_ = l_Lean_stringToMessageData(v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___lam__0(lean_object* v___x_1345_, lean_object* v_ctx_1346_, lean_object* v_mvarId_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_st_mk_ref(v___x_1345_);
v___x_1354_ = l_Lean_Meta_SimpAll_main(v___x_1353_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1382_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1382_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1382_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_st_ref_get(v___x_1353_);
lean_dec(v___x_1353_);
if (lean_obj_tag(v_a_1355_) == 1)
{
lean_object* v_config_1368_; uint8_t v_failIfUnchanged_1369_; 
v_config_1368_ = lean_ctor_get(v_ctx_1346_, 0);
v_failIfUnchanged_1369_ = lean_ctor_get_uint8(v_config_1368_, sizeof(void*)*3 + 13);
if (v_failIfUnchanged_1369_ == 0)
{
goto v___jp_1360_;
}
else
{
lean_object* v_val_1370_; uint8_t v___x_1371_; 
v_val_1370_ = lean_ctor_get(v_a_1355_, 0);
v___x_1371_ = l_Lean_instBEqMVarId_beq(v_mvarId_1347_, v_val_1370_);
if (v___x_1371_ == 0)
{
goto v___jp_1360_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec_ref(v_a_1355_);
lean_dec(v___x_1359_);
lean_del_object(v___x_1357_);
v___x_1372_ = lean_obj_once(&l_Lean_Meta_simpAll___lam__0___closed__1, &l_Lean_Meta_simpAll___lam__0___closed__1_once, _init_l_Lean_Meta_simpAll___lam__0___closed__1);
v___x_1373_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v___x_1372_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
else
{
goto v___jp_1360_;
}
v___jp_1360_:
{
lean_object* v_usedTheorems_1361_; lean_object* v_diag_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v_usedTheorems_1361_ = lean_ctor_get(v___x_1359_, 4);
lean_inc_ref(v_usedTheorems_1361_);
v_diag_1362_ = lean_ctor_get(v___x_1359_, 5);
lean_inc_ref(v_diag_1362_);
lean_dec(v___x_1359_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_usedTheorems_1361_);
lean_ctor_set(v___x_1363_, 1, v_diag_1362_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_a_1355_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1364_);
v___x_1366_ = v___x_1357_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec(v___x_1353_);
v_a_1383_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1354_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1354_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___lam__0___boxed(lean_object* v___x_1391_, lean_object* v_ctx_1392_, lean_object* v_mvarId_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Meta_simpAll___lam__0(v___x_1391_, v_ctx_1392_, v_mvarId_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v_mvarId_1393_);
lean_dec_ref(v_ctx_1392_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll(lean_object* v_mvarId_1402_, lean_object* v_ctx_1403_, lean_object* v_simprocs_1404_, lean_object* v_stats_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_usedTheorems_1411_; lean_object* v_diag_1412_; uint8_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___f_1416_; lean_object* v___x_1417_; 
v_usedTheorems_1411_ = lean_ctor_get(v_stats_1405_, 0);
v_diag_1412_ = lean_ctor_get(v_stats_1405_, 1);
v___x_1413_ = 0;
v___x_1414_ = ((lean_object*)(l_Lean_Meta_simpAll___closed__0));
lean_inc_ref(v_diag_1412_);
lean_inc_ref(v_usedTheorems_1411_);
lean_inc_ref(v_ctx_1403_);
lean_inc(v_mvarId_1402_);
v___x_1415_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1415_, 0, v_mvarId_1402_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
lean_ctor_set(v___x_1415_, 2, v_ctx_1403_);
lean_ctor_set(v___x_1415_, 3, v_simprocs_1404_);
lean_ctor_set(v___x_1415_, 4, v_usedTheorems_1411_);
lean_ctor_set(v___x_1415_, 5, v_diag_1412_);
lean_ctor_set_uint8(v___x_1415_, sizeof(void*)*6, v___x_1413_);
lean_inc(v_mvarId_1402_);
v___f_1416_ = lean_alloc_closure((void*)(l_Lean_Meta_simpAll___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1416_, 0, v___x_1415_);
lean_closure_set(v___f_1416_, 1, v_ctx_1403_);
lean_closure_set(v___f_1416_, 2, v_mvarId_1402_);
v___x_1417_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1402_, v___f_1416_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___boxed(lean_object* v_mvarId_1418_, lean_object* v_ctx_1419_, lean_object* v_simprocs_1420_, lean_object* v_stats_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_Meta_simpAll(v_mvarId_1418_, v_ctx_1419_, v_simprocs_1420_, v_stats_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec_ref(v_stats_1421_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(lean_object* v_00_u03b1_1428_, lean_object* v_msg_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v_msg_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___boxed(lean_object* v_00_u03b1_1436_, lean_object* v_msg_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(v_00_u03b1_1436_, v_msg_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1513_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__4___redArg___closed__5));
v___x_1514_ = 0;
v___x_1515_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_));
v___x_1516_ = l_Lean_registerTraceClass(v___x_1513_, v___x_1514_, v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2____boxed(lean_object* v_a_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_();
return v_res_1518_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_SimpAll(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_SimpAll_instInhabitedEntry_default = _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default();
lean_mark_persistent(l_Lean_Meta_SimpAll_instInhabitedEntry_default);
l_Lean_Meta_SimpAll_instInhabitedEntry = _init_l_Lean_Meta_SimpAll_instInhabitedEntry();
lean_mark_persistent(l_Lean_Meta_SimpAll_instInhabitedEntry);
res = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_SimpAll(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_SimpAll(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_SimpAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_SimpAll(builtin);
}
#ifdef __cplusplus
}
#endif
