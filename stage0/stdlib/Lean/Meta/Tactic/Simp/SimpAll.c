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
lean_object* l_Lean_Meta_SimpTheoremsArray_eraseTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setSimpTheorems(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedOrigin_default;
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
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "↓ "};
static const lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 4, .m_data = "↓ ← "};
static const lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3;
static const lean_string_object l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "← "};
static const lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0___boxed(lean_object**);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 18, 104, 2, 176, 25, 65, 55)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(238, 191, 30, 88, 6, 20, 173, 203)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__7_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "entry.id: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__9_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__11_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__13_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 169, 0, 235, 118, 49, 137, 5)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 101, 77, 233, 232, 200, 249, 82)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 207, 103, 84, 232, 152, 203, 58)}};
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
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_obj_once(&l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2, &l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2_once, _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__2);
v___x_8_ = l_Lean_Meta_instInhabitedOrigin_default;
v___x_9_ = lean_box(0);
v___x_10_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v___x_7_);
lean_ctor_set(v___x_10_, 4, v___x_7_);
lean_ctor_set(v___x_10_, 5, v___x_7_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3, &l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3_once, _init_l_Lean_Meta_SimpAll_instInhabitedEntry_default___closed__3);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Meta_SimpAll_instInhabitedEntry(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Meta_SimpAll_instInhabitedEntry_default;
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0(lean_object* v_x_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
lean_inc(v___y_14_);
v___x_20_ = lean_apply_6(v_x_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, lean_box(0));
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0___boxed(lean_object* v_x_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0(v_x_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_22_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(lean_object* v_mvarId_29_, lean_object* v_x_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___f_37_; lean_object* v___x_38_; 
lean_inc(v___y_31_);
v___f_37_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_37_, 0, v_x_30_);
lean_closure_set(v___f_37_, 1, v___y_31_);
v___x_38_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_29_, v___f_37_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
if (lean_obj_tag(v___x_38_) == 0)
{
return v___x_38_;
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_38_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_38_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___boxed(lean_object* v_mvarId_47_, lean_object* v_x_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_47_, v_x_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0(lean_object* v_00_u03b1_56_, lean_object* v_mvarId_57_, lean_object* v_x_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_57_, v_x_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___boxed(lean_object* v_00_u03b1_66_, lean_object* v_mvarId_67_, lean_object* v_x_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0(v_00_u03b1_66_, v_mvarId_67_, v_x_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v___y_69_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(lean_object* v_e_76_, lean_object* v___y_77_){
_start:
{
uint8_t v___x_79_; 
v___x_79_ = l_Lean_Expr_hasMVar(v_e_76_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v_e_76_);
return v___x_80_;
}
else
{
lean_object* v___x_81_; lean_object* v_mctx_82_; lean_object* v___x_83_; lean_object* v_fst_84_; lean_object* v_snd_85_; lean_object* v___x_86_; lean_object* v_cache_87_; lean_object* v_zetaDeltaFVarIds_88_; lean_object* v_postponed_89_; lean_object* v_diag_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_99_; 
v___x_81_ = lean_st_ref_get(v___y_77_);
v_mctx_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc_ref(v_mctx_82_);
lean_dec(v___x_81_);
v___x_83_ = l_Lean_instantiateMVarsCore(v_mctx_82_, v_e_76_);
v_fst_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_fst_84_);
v_snd_85_ = lean_ctor_get(v___x_83_, 1);
lean_inc(v_snd_85_);
lean_dec_ref(v___x_83_);
v___x_86_ = lean_st_ref_take(v___y_77_);
v_cache_87_ = lean_ctor_get(v___x_86_, 1);
v_zetaDeltaFVarIds_88_ = lean_ctor_get(v___x_86_, 2);
v_postponed_89_ = lean_ctor_get(v___x_86_, 3);
v_diag_90_ = lean_ctor_get(v___x_86_, 4);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_99_ == 0)
{
lean_object* v_unused_100_; 
v_unused_100_ = lean_ctor_get(v___x_86_, 0);
lean_dec(v_unused_100_);
v___x_92_ = v___x_86_;
v_isShared_93_ = v_isSharedCheck_99_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_diag_90_);
lean_inc(v_postponed_89_);
lean_inc(v_zetaDeltaFVarIds_88_);
lean_inc(v_cache_87_);
lean_dec(v___x_86_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_99_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v_snd_85_);
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_snd_85_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_cache_87_);
lean_ctor_set(v_reuseFailAlloc_98_, 2, v_zetaDeltaFVarIds_88_);
lean_ctor_set(v_reuseFailAlloc_98_, 3, v_postponed_89_);
lean_ctor_set(v_reuseFailAlloc_98_, 4, v_diag_90_);
v___x_95_ = v_reuseFailAlloc_98_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_st_ref_put(v___y_77_, v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v_fst_84_);
return v___x_97_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg___boxed(lean_object* v_e_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(v_e_101_, v___y_102_);
lean_dec(v___y_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2(lean_object* v_e_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(v_e_105_, v___y_108_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___boxed(lean_object* v_e_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2(v_e_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0(lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Meta_getPropHyps(v___y_122_, v___y_123_, v___y_124_, v___y_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0___boxed(lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0(v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
return v_res_134_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(lean_object* v_a_135_, lean_object* v_as_136_, size_t v_i_137_, size_t v_stop_138_){
_start:
{
uint8_t v___x_139_; 
v___x_139_ = lean_usize_dec_eq(v_i_137_, v_stop_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = lean_array_uget_borrowed(v_as_136_, v_i_137_);
v___x_141_ = l_Lean_instBEqFVarId_beq(v_a_135_, v___x_140_);
if (v___x_141_ == 0)
{
size_t v___x_142_; size_t v___x_143_; 
v___x_142_ = ((size_t)1ULL);
v___x_143_ = lean_usize_add(v_i_137_, v___x_142_);
v_i_137_ = v___x_143_;
goto _start;
}
else
{
return v___x_141_;
}
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1___boxed(lean_object* v_a_146_, lean_object* v_as_147_, lean_object* v_i_148_, lean_object* v_stop_149_){
_start:
{
size_t v_i_boxed_150_; size_t v_stop_boxed_151_; uint8_t v_res_152_; lean_object* v_r_153_; 
v_i_boxed_150_ = lean_unbox_usize(v_i_148_);
lean_dec(v_i_148_);
v_stop_boxed_151_ = lean_unbox_usize(v_stop_149_);
lean_dec(v_stop_149_);
v_res_152_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(v_a_146_, v_as_147_, v_i_boxed_150_, v_stop_boxed_151_);
lean_dec_ref(v_as_147_);
lean_dec(v_a_146_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(lean_object* v_as_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_array_get_size(v_as_154_);
v___x_158_ = lean_nat_dec_lt(v___x_156_, v___x_157_);
if (v___x_158_ == 0)
{
return v___x_158_;
}
else
{
if (v___x_158_ == 0)
{
return v___x_158_;
}
else
{
size_t v___x_159_; size_t v___x_160_; uint8_t v___x_161_; 
v___x_159_ = ((size_t)0ULL);
v___x_160_ = lean_usize_of_nat(v___x_157_);
v___x_161_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(v_a_155_, v_as_154_, v___x_159_, v___x_160_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1___boxed(lean_object* v_as_162_, lean_object* v_a_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(v_as_162_, v_a_163_);
lean_dec(v_a_163_);
lean_dec_ref(v_as_162_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(lean_object* v_a_166_, lean_object* v_as_167_, size_t v_sz_168_, size_t v_i_169_, lean_object* v_b_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_a_178_; uint8_t v___x_182_; 
v___x_182_ = lean_usize_dec_lt(v_i_169_, v_sz_168_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; 
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v_b_170_);
return v___x_183_;
}
else
{
lean_object* v_a_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_a_184_ = lean_array_uget_borrowed(v_as_167_, v_i_169_);
lean_inc(v_a_184_);
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v_a_184_);
v___x_186_ = l_Lean_Meta_SimpTheoremsArray_isErased(v_b_170_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_inc(v_a_184_);
v___x_187_ = l_Lean_FVarId_getDecl___redArg(v_a_184_, v___y_172_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v_ctx_191_; lean_object* v_indexConfig_192_; lean_object* v___x_193_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc_n(v_a_188_, 2);
lean_dec_ref_known(v___x_187_, 1);
v___x_189_ = l_Lean_LocalDecl_toExpr(v_a_188_);
v___x_190_ = lean_st_ref_get(v___y_171_);
v_ctx_191_ = lean_ctor_get(v___x_190_, 2);
lean_inc_ref(v_ctx_191_);
lean_dec(v___x_190_);
v_indexConfig_192_ = lean_ctor_get(v_ctx_191_, 5);
lean_inc_ref(v_indexConfig_192_);
lean_dec_ref(v_ctx_191_);
lean_inc_ref(v___x_189_);
lean_inc_ref(v___x_185_);
v___x_193_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v_b_170_, v___x_185_, v___x_189_, v_indexConfig_192_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_195_; uint8_t v_modified_196_; lean_object* v_mvarId_197_; lean_object* v_entries_198_; lean_object* v_ctx_199_; lean_object* v_simprocs_200_; lean_object* v_usedTheorems_201_; lean_object* v_diag_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_242_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_193_, 1);
v___x_195_ = lean_st_ref_take(v___y_171_);
v_modified_196_ = lean_ctor_get_uint8(v___x_195_, sizeof(void*)*6);
v_mvarId_197_ = lean_ctor_get(v___x_195_, 0);
v_entries_198_ = lean_ctor_get(v___x_195_, 1);
v_ctx_199_ = lean_ctor_get(v___x_195_, 2);
v_simprocs_200_ = lean_ctor_get(v___x_195_, 3);
v_usedTheorems_201_ = lean_ctor_get(v___x_195_, 4);
v_diag_202_ = lean_ctor_get(v___x_195_, 5);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_242_ == 0)
{
v___x_204_ = v___x_195_;
v_isShared_205_ = v_isSharedCheck_242_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_diag_202_);
lean_inc(v_usedTheorems_201_);
lean_inc(v_simprocs_200_);
lean_inc(v_ctx_199_);
lean_inc(v_entries_198_);
lean_inc(v_mvarId_197_);
lean_dec(v___x_195_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_242_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_208_; 
lean_inc(v_a_194_);
v___x_206_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v_ctx_199_, v_a_194_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 2, v___x_206_);
v___x_208_ = v___x_204_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_mvarId_197_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_entries_198_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_simprocs_200_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_usedTheorems_201_);
lean_ctor_set(v_reuseFailAlloc_241_, 5, v_diag_202_);
lean_ctor_set_uint8(v_reuseFailAlloc_241_, sizeof(void*)*6, v_modified_196_);
v___x_208_ = v_reuseFailAlloc_241_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = lean_st_ref_put(v___y_171_, v___x_208_);
v___x_210_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(v_a_166_, v_a_184_);
if (v___x_210_ == 0)
{
lean_dec_ref(v___x_189_);
lean_dec(v_a_188_);
lean_dec_ref_known(v___x_185_, 1);
v_a_178_ = v_a_194_;
goto v___jp_177_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = l_Lean_LocalDecl_type(v_a_188_);
v___x_212_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(v___x_211_, v___y_173_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v_modified_217_; lean_object* v_mvarId_218_; lean_object* v_entries_219_; lean_object* v_ctx_220_; lean_object* v_simprocs_221_; lean_object* v_usedTheorems_222_; lean_object* v_diag_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_232_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc_n(v_a_213_, 2);
lean_dec_ref_known(v___x_212_, 1);
v___x_214_ = l_Lean_LocalDecl_userName(v_a_188_);
lean_dec(v_a_188_);
lean_inc(v_a_184_);
v___x_215_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_215_, 0, v_a_184_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
lean_ctor_set(v___x_215_, 2, v___x_185_);
lean_ctor_set(v___x_215_, 3, v_a_213_);
lean_ctor_set(v___x_215_, 4, v_a_213_);
lean_ctor_set(v___x_215_, 5, v___x_189_);
v___x_216_ = lean_st_ref_take(v___y_171_);
v_modified_217_ = lean_ctor_get_uint8(v___x_216_, sizeof(void*)*6);
v_mvarId_218_ = lean_ctor_get(v___x_216_, 0);
v_entries_219_ = lean_ctor_get(v___x_216_, 1);
v_ctx_220_ = lean_ctor_get(v___x_216_, 2);
v_simprocs_221_ = lean_ctor_get(v___x_216_, 3);
v_usedTheorems_222_ = lean_ctor_get(v___x_216_, 4);
v_diag_223_ = lean_ctor_get(v___x_216_, 5);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_232_ == 0)
{
v___x_225_ = v___x_216_;
v_isShared_226_ = v_isSharedCheck_232_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_diag_223_);
lean_inc(v_usedTheorems_222_);
lean_inc(v_simprocs_221_);
lean_inc(v_ctx_220_);
lean_inc(v_entries_219_);
lean_inc(v_mvarId_218_);
lean_dec(v___x_216_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_232_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_array_push(v_entries_219_, v___x_215_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_227_);
v___x_229_ = v___x_225_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_mvarId_218_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_ctx_220_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_simprocs_221_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_usedTheorems_222_);
lean_ctor_set(v_reuseFailAlloc_231_, 5, v_diag_223_);
lean_ctor_set_uint8(v_reuseFailAlloc_231_, sizeof(void*)*6, v_modified_217_);
v___x_229_ = v_reuseFailAlloc_231_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; 
v___x_230_ = lean_st_ref_put(v___y_171_, v___x_229_);
v_a_178_ = v_a_194_;
goto v___jp_177_;
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec(v_a_194_);
lean_dec_ref(v___x_189_);
lean_dec(v_a_188_);
lean_dec_ref_known(v___x_185_, 1);
v_a_233_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_212_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_212_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_189_);
lean_dec(v_a_188_);
lean_dec_ref_known(v___x_185_, 1);
return v___x_193_;
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec_ref_known(v___x_185_, 1);
lean_dec_ref(v_b_170_);
v_a_243_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_187_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_187_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_185_, 1);
v_a_178_ = v_b_170_;
goto v___jp_177_;
}
}
v___jp_177_:
{
size_t v___x_179_; size_t v___x_180_; 
v___x_179_ = ((size_t)1ULL);
v___x_180_ = lean_usize_add(v_i_169_, v___x_179_);
v_i_169_ = v___x_180_;
v_b_170_ = v_a_178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3___boxed(lean_object* v_a_251_, lean_object* v_as_252_, lean_object* v_sz_253_, lean_object* v_i_254_, lean_object* v_b_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
size_t v_sz_boxed_262_; size_t v_i_boxed_263_; lean_object* v_res_264_; 
v_sz_boxed_262_ = lean_unbox_usize(v_sz_253_);
lean_dec(v_sz_253_);
v_i_boxed_263_ = lean_unbox_usize(v_i_254_);
lean_dec(v_i_254_);
v_res_264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(v_a_251_, v_as_252_, v_sz_boxed_262_, v_i_boxed_263_, v_b_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v_as_252_);
lean_dec_ref(v_a_251_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___f_272_; lean_object* v___x_273_; lean_object* v_mvarId_274_; lean_object* v___x_275_; 
v___f_272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___closed__0));
v___x_273_ = lean_st_ref_get(v_a_266_);
v_mvarId_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_mvarId_274_);
lean_dec(v___x_273_);
v___x_275_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_274_, v___f_272_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; lean_object* v_mvarId_278_; lean_object* v___x_279_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
v___x_277_ = lean_st_ref_get(v_a_266_);
v_mvarId_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_mvarId_278_);
lean_dec(v___x_277_);
v___x_279_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_278_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_281_; lean_object* v_ctx_282_; lean_object* v_simpTheorems_283_; size_t v_sz_284_; size_t v___x_285_; lean_object* v___x_286_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_a_280_);
lean_dec_ref_known(v___x_279_, 1);
v___x_281_ = lean_st_ref_get(v_a_266_);
v_ctx_282_ = lean_ctor_get(v___x_281_, 2);
lean_inc_ref(v_ctx_282_);
lean_dec(v___x_281_);
v_simpTheorems_283_ = lean_ctor_get(v_ctx_282_, 6);
lean_inc_ref(v_simpTheorems_283_);
lean_dec_ref(v_ctx_282_);
v_sz_284_ = lean_array_size(v_a_276_);
v___x_285_ = ((size_t)0ULL);
v___x_286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(v_a_280_, v_a_276_, v_sz_284_, v___x_285_, v_simpTheorems_283_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
lean_dec(v_a_276_);
lean_dec(v_a_280_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_294_; 
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v___x_286_, 0);
lean_dec(v_unused_295_);
v___x_288_ = v___x_286_;
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
else
{
lean_dec(v___x_286_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = lean_box(0);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_290_);
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
v_a_296_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_286_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_286_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec(v_a_276_);
v_a_304_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_279_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_279_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
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
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v_a_312_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_275_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_275_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___boxed(lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg(lean_object* v_a_327_){
_start:
{
lean_object* v___x_329_; lean_object* v_ctx_330_; lean_object* v_simpTheorems_331_; lean_object* v___x_332_; 
v___x_329_ = lean_st_ref_get(v_a_327_);
v_ctx_330_ = lean_ctor_get(v___x_329_, 2);
lean_inc_ref(v_ctx_330_);
lean_dec(v___x_329_);
v_simpTheorems_331_ = lean_ctor_get(v_ctx_330_, 6);
lean_inc_ref(v_simpTheorems_331_);
lean_dec_ref(v_ctx_330_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v_simpTheorems_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg___boxed(lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg(v_a_333_);
lean_dec(v_a_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_342_; lean_object* v_ctx_343_; lean_object* v_simpTheorems_344_; lean_object* v___x_345_; 
v___x_342_ = lean_st_ref_get(v_a_336_);
v_ctx_343_ = lean_ctor_get(v___x_342_, 2);
lean_inc_ref(v_ctx_343_);
lean_dec(v___x_342_);
v_simpTheorems_344_ = lean_ctor_get(v_ctx_343_, 6);
lean_inc_ref(v_simpTheorems_344_);
lean_dec_ref(v_ctx_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v_simpTheorems_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___boxed(lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; lean_object* v_ngen_356_; lean_object* v_namePrefix_357_; lean_object* v_idx_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_388_; 
v___x_355_ = lean_st_ref_get(v___y_353_);
v_ngen_356_ = lean_ctor_get(v___x_355_, 2);
lean_inc_ref(v_ngen_356_);
lean_dec(v___x_355_);
v_namePrefix_357_ = lean_ctor_get(v_ngen_356_, 0);
v_idx_358_ = lean_ctor_get(v_ngen_356_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v_ngen_356_);
if (v_isSharedCheck_388_ == 0)
{
v___x_360_ = v_ngen_356_;
v_isShared_361_ = v_isSharedCheck_388_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_idx_358_);
lean_inc(v_namePrefix_357_);
lean_dec(v_ngen_356_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_388_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_r_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
lean_inc(v_idx_358_);
lean_inc(v_namePrefix_357_);
v_r_362_ = l_Lean_Name_num___override(v_namePrefix_357_, v_idx_358_);
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = lean_nat_add(v_idx_358_, v___x_363_);
lean_dec(v_idx_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_364_);
v___x_366_ = v___x_360_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_namePrefix_357_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_387_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v_env_368_; lean_object* v_nextMacroScope_369_; lean_object* v_auxDeclNGen_370_; lean_object* v_traceState_371_; lean_object* v_cache_372_; lean_object* v_recordedDeps_373_; lean_object* v_messages_374_; lean_object* v_infoState_375_; lean_object* v_snapshotTasks_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_385_; 
v___x_367_ = lean_st_ref_take(v___y_353_);
v_env_368_ = lean_ctor_get(v___x_367_, 0);
v_nextMacroScope_369_ = lean_ctor_get(v___x_367_, 1);
v_auxDeclNGen_370_ = lean_ctor_get(v___x_367_, 3);
v_traceState_371_ = lean_ctor_get(v___x_367_, 4);
v_cache_372_ = lean_ctor_get(v___x_367_, 5);
v_recordedDeps_373_ = lean_ctor_get(v___x_367_, 6);
v_messages_374_ = lean_ctor_get(v___x_367_, 7);
v_infoState_375_ = lean_ctor_get(v___x_367_, 8);
v_snapshotTasks_376_ = lean_ctor_get(v___x_367_, 9);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; 
v_unused_386_ = lean_ctor_get(v___x_367_, 2);
lean_dec(v_unused_386_);
v___x_378_ = v___x_367_;
v_isShared_379_ = v_isSharedCheck_385_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_snapshotTasks_376_);
lean_inc(v_infoState_375_);
lean_inc(v_messages_374_);
lean_inc(v_recordedDeps_373_);
lean_inc(v_cache_372_);
lean_inc(v_traceState_371_);
lean_inc(v_auxDeclNGen_370_);
lean_inc(v_nextMacroScope_369_);
lean_inc(v_env_368_);
lean_dec(v___x_367_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_385_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 2, v___x_366_);
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_env_368_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_nextMacroScope_369_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_384_, 3, v_auxDeclNGen_370_);
lean_ctor_set(v_reuseFailAlloc_384_, 4, v_traceState_371_);
lean_ctor_set(v_reuseFailAlloc_384_, 5, v_cache_372_);
lean_ctor_set(v_reuseFailAlloc_384_, 6, v_recordedDeps_373_);
lean_ctor_set(v_reuseFailAlloc_384_, 7, v_messages_374_);
lean_ctor_set(v_reuseFailAlloc_384_, 8, v_infoState_375_);
lean_ctor_set(v_reuseFailAlloc_384_, 9, v_snapshotTasks_376_);
v___x_381_ = v_reuseFailAlloc_384_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_st_ref_put(v___y_353_, v___x_381_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v_r_362_);
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
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0));
v___x_408_ = l_Lean_stringToMessageData(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__2));
v___x_411_ = l_Lean_stringToMessageData(v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__4));
v___x_414_ = l_Lean_stringToMessageData(v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(lean_object* v_x_415_){
_start:
{
switch(lean_obj_tag(v_x_415_))
{
case 0:
{
lean_object* v_declName_417_; uint8_t v_post_418_; uint8_t v_inv_419_; uint8_t v___x_420_; lean_object* v_r_421_; 
v_declName_417_ = lean_ctor_get(v_x_415_, 0);
lean_inc(v_declName_417_);
v_post_418_ = lean_ctor_get_uint8(v_x_415_, sizeof(void*)*1);
v_inv_419_ = lean_ctor_get_uint8(v_x_415_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_x_415_, 1);
v___x_420_ = 0;
v_r_421_ = l_Lean_MessageData_ofConstName(v_declName_417_, v___x_420_);
if (v_post_418_ == 0)
{
if (v_inv_419_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1);
v___x_423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v_r_421_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v_r_421_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
}
else
{
if (v_inv_419_ == 0)
{
lean_object* v___x_428_; 
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v_r_421_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_r_421_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
}
case 1:
{
lean_object* v_fvarId_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_441_; 
v_fvarId_432_ = lean_ctor_get(v_x_415_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_415_);
if (v_isSharedCheck_441_ == 0)
{
v___x_434_ = v_x_415_;
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_fvarId_432_);
lean_dec(v_x_415_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_436_ = l_Lean_mkFVar(v_fvarId_432_);
v___x_437_ = l_Lean_MessageData_ofExpr(v___x_436_);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 0);
lean_ctor_set(v___x_434_, 0, v___x_437_);
v___x_439_ = v___x_434_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
case 2:
{
lean_object* v_ref_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_ref_442_ = lean_ctor_get(v_x_415_, 1);
lean_inc(v_ref_442_);
lean_dec_ref_known(v_x_415_, 2);
v___x_443_ = l_Lean_MessageData_ofSyntax(v_ref_442_);
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
default: 
{
lean_object* v_name_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_453_; 
v_name_445_ = lean_ctor_get(v_x_415_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v_x_415_);
if (v_isSharedCheck_453_ == 0)
{
v___x_447_ = v_x_415_;
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_name_445_);
lean_dec(v_x_415_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = l_Lean_MessageData_ofName(v_name_445_);
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 0);
lean_ctor_set(v___x_447_, 0, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___boxed(lean_object* v_x_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_x_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1(lean_object* v_x_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_x_457_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___boxed(lean_object* v_x_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1(v_x_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(lean_object* v_msgData_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; lean_object* v_env_480_; lean_object* v___x_481_; lean_object* v_toCold_482_; lean_object* v_mctx_483_; lean_object* v_lctx_484_; lean_object* v_options_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_479_ = lean_st_ref_get(v___y_477_);
v_env_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc_ref(v_env_480_);
lean_dec(v___x_479_);
v___x_481_ = lean_st_ref_get(v___y_475_);
v_toCold_482_ = lean_ctor_get(v___y_476_, 0);
v_mctx_483_ = lean_ctor_get(v___x_481_, 0);
lean_inc_ref(v_mctx_483_);
lean_dec(v___x_481_);
v_lctx_484_ = lean_ctor_get(v___y_474_, 2);
v_options_485_ = lean_ctor_get(v_toCold_482_, 2);
lean_inc_ref(v_options_485_);
lean_inc_ref(v_lctx_484_);
v___x_486_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_486_, 0, v_env_480_);
lean_ctor_set(v___x_486_, 1, v_mctx_483_);
lean_ctor_set(v___x_486_, 2, v_lctx_484_);
lean_ctor_set(v___x_486_, 3, v_options_485_);
v___x_487_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v_msgData_473_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2___boxed(lean_object* v_msgData_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msgData_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_495_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_496_; double v___x_497_; 
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = lean_float_of_nat(v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(lean_object* v_cls_501_, lean_object* v_msg_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_ref_508_; lean_object* v___x_509_; lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_555_; 
v_ref_508_ = lean_ctor_get(v___y_505_, 2);
v___x_509_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msg_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_555_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_555_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_555_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v_traceState_515_; lean_object* v_env_516_; lean_object* v_nextMacroScope_517_; lean_object* v_ngen_518_; lean_object* v_auxDeclNGen_519_; lean_object* v_cache_520_; lean_object* v_recordedDeps_521_; lean_object* v_messages_522_; lean_object* v_infoState_523_; lean_object* v_snapshotTasks_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_554_; 
v___x_514_ = lean_st_ref_take(v___y_506_);
v_traceState_515_ = lean_ctor_get(v___x_514_, 4);
v_env_516_ = lean_ctor_get(v___x_514_, 0);
v_nextMacroScope_517_ = lean_ctor_get(v___x_514_, 1);
v_ngen_518_ = lean_ctor_get(v___x_514_, 2);
v_auxDeclNGen_519_ = lean_ctor_get(v___x_514_, 3);
v_cache_520_ = lean_ctor_get(v___x_514_, 5);
v_recordedDeps_521_ = lean_ctor_get(v___x_514_, 6);
v_messages_522_ = lean_ctor_get(v___x_514_, 7);
v_infoState_523_ = lean_ctor_get(v___x_514_, 8);
v_snapshotTasks_524_ = lean_ctor_get(v___x_514_, 9);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_554_ == 0)
{
v___x_526_ = v___x_514_;
v_isShared_527_ = v_isSharedCheck_554_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_snapshotTasks_524_);
lean_inc(v_infoState_523_);
lean_inc(v_messages_522_);
lean_inc(v_recordedDeps_521_);
lean_inc(v_cache_520_);
lean_inc(v_traceState_515_);
lean_inc(v_auxDeclNGen_519_);
lean_inc(v_ngen_518_);
lean_inc(v_nextMacroScope_517_);
lean_inc(v_env_516_);
lean_dec(v___x_514_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_554_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
uint64_t v_tid_528_; lean_object* v_traces_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_553_; 
v_tid_528_ = lean_ctor_get_uint64(v_traceState_515_, sizeof(void*)*1);
v_traces_529_ = lean_ctor_get(v_traceState_515_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v_traceState_515_);
if (v_isSharedCheck_553_ == 0)
{
v___x_531_ = v_traceState_515_;
v_isShared_532_ = v_isSharedCheck_553_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_traces_529_);
lean_dec(v_traceState_515_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_553_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; double v___x_535_; uint8_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_533_ = lean_box(0);
v___x_534_ = lean_box(0);
v___x_535_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0);
v___x_536_ = 0;
v___x_537_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1));
v___x_538_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_538_, 0, v_cls_501_);
lean_ctor_set(v___x_538_, 1, v___x_534_);
lean_ctor_set(v___x_538_, 2, v___x_537_);
lean_ctor_set_float(v___x_538_, sizeof(void*)*3, v___x_535_);
lean_ctor_set_float(v___x_538_, sizeof(void*)*3 + 8, v___x_535_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*3 + 16, v___x_536_);
v___x_539_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2));
v___x_540_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v_a_510_);
lean_ctor_set(v___x_540_, 2, v___x_539_);
lean_inc(v_ref_508_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v_ref_508_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = l_Lean_PersistentArray_push___redArg(v_traces_529_, v___x_541_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_542_);
v___x_544_ = v___x_531_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_542_);
lean_ctor_set_uint64(v_reuseFailAlloc_552_, sizeof(void*)*1, v_tid_528_);
v___x_544_ = v_reuseFailAlloc_552_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_546_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 4, v___x_544_);
v___x_546_ = v___x_526_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_env_516_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_nextMacroScope_517_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_ngen_518_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_auxDeclNGen_519_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_551_, 5, v_cache_520_);
lean_ctor_set(v_reuseFailAlloc_551_, 6, v_recordedDeps_521_);
lean_ctor_set(v_reuseFailAlloc_551_, 7, v_messages_522_);
lean_ctor_set(v_reuseFailAlloc_551_, 8, v_infoState_523_);
lean_ctor_set(v_reuseFailAlloc_551_, 9, v_snapshotTasks_524_);
v___x_546_ = v_reuseFailAlloc_551_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_st_ref_put(v___y_506_, v___x_546_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_533_);
v___x_549_ = v___x_512_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_533_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___boxed(lean_object* v_cls_556_, lean_object* v_msg_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_cls_556_, v_msg_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(lean_object* v_fvarId_564_, lean_object* v_fst_565_, lean_object* v_snd_566_, lean_object* v___x_567_, uint8_t v___x_568_, lean_object* v___x_569_, lean_object* v_a_570_, lean_object* v___x_571_, lean_object* v_userName_572_, lean_object* v_origType_573_, lean_object* v_____r_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; lean_object* v_ctx_582_; lean_object* v_simpTheorems_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_581_ = lean_st_ref_get(v___y_575_);
v_ctx_582_ = lean_ctor_get(v___x_581_, 2);
lean_inc_ref(v_ctx_582_);
lean_dec(v___x_581_);
v_simpTheorems_583_ = lean_ctor_get(v_ctx_582_, 6);
lean_inc_ref(v_simpTheorems_583_);
lean_dec_ref(v_ctx_582_);
lean_inc(v_fvarId_564_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v_fvarId_564_);
v___x_585_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(v_simpTheorems_583_, v___x_584_);
v___x_586_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_579_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
lean_inc_ref(v_snd_566_);
lean_inc_ref(v_fst_565_);
v___x_588_ = l_Lean_Meta_mkExpectedTypeHint(v_fst_565_, v_snd_566_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v_indexConfig_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v_indexConfig_590_ = lean_ctor_get(v___x_567_, 5);
v___x_591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_591_, 0, v_a_587_);
lean_inc_ref(v_indexConfig_590_);
lean_inc_ref(v___x_591_);
v___x_592_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v___x_585_, v___x_591_, v_a_589_, v_indexConfig_590_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_624_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_624_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_624_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_624_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v_mvarId_598_; lean_object* v_entries_599_; lean_object* v_simprocs_600_; lean_object* v_usedTheorems_601_; lean_object* v_diag_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_622_; 
v___x_597_ = lean_st_ref_take(v___y_575_);
v_mvarId_598_ = lean_ctor_get(v___x_597_, 0);
v_entries_599_ = lean_ctor_get(v___x_597_, 1);
v_simprocs_600_ = lean_ctor_get(v___x_597_, 3);
v_usedTheorems_601_ = lean_ctor_get(v___x_597_, 4);
v_diag_602_ = lean_ctor_get(v___x_597_, 5);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v___x_597_, 2);
lean_dec(v_unused_623_);
v___x_604_ = v___x_597_;
v_isShared_605_ = v_isSharedCheck_622_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_diag_602_);
lean_inc(v_usedTheorems_601_);
lean_inc(v_simprocs_600_);
lean_inc(v_entries_599_);
lean_inc(v_mvarId_598_);
lean_dec(v___x_597_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_622_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___y_607_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_array_get_size(v_entries_599_);
v___x_618_ = lean_nat_dec_lt(v_a_570_, v___x_617_);
if (v___x_618_ == 0)
{
lean_dec_ref_known(v___x_591_, 1);
lean_dec_ref(v_origType_573_);
lean_dec(v_userName_572_);
lean_dec_ref(v_snd_566_);
lean_dec_ref(v_fst_565_);
lean_dec(v_fvarId_564_);
v___y_607_ = v_entries_599_;
goto v___jp_606_;
}
else
{
lean_object* v_xs_x27_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_xs_x27_619_ = lean_array_fset(v_entries_599_, v_a_570_, v___x_571_);
v___x_620_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_620_, 0, v_fvarId_564_);
lean_ctor_set(v___x_620_, 1, v_userName_572_);
lean_ctor_set(v___x_620_, 2, v___x_591_);
lean_ctor_set(v___x_620_, 3, v_origType_573_);
lean_ctor_set(v___x_620_, 4, v_snd_566_);
lean_ctor_set(v___x_620_, 5, v_fst_565_);
v___x_621_ = lean_array_fset(v_xs_x27_619_, v_a_570_, v___x_620_);
v___y_607_ = v___x_621_;
goto v___jp_606_;
}
v___jp_606_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v___x_567_, v_a_593_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 2, v___x_608_);
lean_ctor_set(v___x_604_, 1, v___y_607_);
v___x_610_ = v___x_604_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_mvarId_598_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___y_607_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_simprocs_600_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_usedTheorems_601_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v_diag_602_);
v___x_610_ = v_reuseFailAlloc_616_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*6, v___x_568_);
v___x_611_ = lean_st_ref_put(v___y_575_, v___x_610_);
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_569_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_612_);
v___x_614_ = v___x_595_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref_known(v___x_591_, 1);
lean_dec_ref(v_origType_573_);
lean_dec(v_userName_572_);
lean_dec_ref(v___x_569_);
lean_dec_ref(v___x_567_);
lean_dec_ref(v_snd_566_);
lean_dec_ref(v_fst_565_);
lean_dec(v_fvarId_564_);
v_a_625_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_592_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_592_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_a_587_);
lean_dec_ref(v___x_585_);
lean_dec_ref(v_origType_573_);
lean_dec(v_userName_572_);
lean_dec_ref(v___x_569_);
lean_dec_ref(v___x_567_);
lean_dec_ref(v_snd_566_);
lean_dec_ref(v_fst_565_);
lean_dec(v_fvarId_564_);
v_a_633_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_588_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_588_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec_ref(v___x_585_);
lean_dec_ref(v_origType_573_);
lean_dec(v_userName_572_);
lean_dec_ref(v___x_569_);
lean_dec_ref(v___x_567_);
lean_dec_ref(v_snd_566_);
lean_dec_ref(v_fst_565_);
lean_dec(v_fvarId_564_);
v_a_641_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_586_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_586_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_fvarId_649_ = _args[0];
lean_object* v_fst_650_ = _args[1];
lean_object* v_snd_651_ = _args[2];
lean_object* v___x_652_ = _args[3];
lean_object* v___x_653_ = _args[4];
lean_object* v___x_654_ = _args[5];
lean_object* v_a_655_ = _args[6];
lean_object* v___x_656_ = _args[7];
lean_object* v_userName_657_ = _args[8];
lean_object* v_origType_658_ = _args[9];
lean_object* v_____r_659_ = _args[10];
lean_object* v___y_660_ = _args[11];
lean_object* v___y_661_ = _args[12];
lean_object* v___y_662_ = _args[13];
lean_object* v___y_663_ = _args[14];
lean_object* v___y_664_ = _args[15];
lean_object* v___y_665_ = _args[16];
_start:
{
uint8_t v___x_24977__boxed_666_; lean_object* v_res_667_; 
v___x_24977__boxed_666_ = lean_unbox(v___x_653_);
v_res_667_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fvarId_649_, v_fst_650_, v_snd_651_, v___x_652_, v___x_24977__boxed_666_, v___x_654_, v_a_655_, v___x_656_, v_userName_657_, v_origType_658_, v_____r_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec(v_a_655_);
return v_res_667_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_684_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__7));
v___x_685_ = l_Lean_Name_append(v___x_684_, v___x_683_);
return v___x_685_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__9));
v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__11));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__13));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(lean_object* v_upperBound_695_, lean_object* v___x_696_, lean_object* v___x_697_, lean_object* v_a_698_, lean_object* v_b_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_a_707_; lean_object* v___y_712_; uint8_t v___x_731_; 
v___x_731_ = lean_nat_dec_lt(v_a_698_, v_upperBound_695_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
lean_dec(v_a_698_);
lean_dec_ref(v___x_697_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v_b_699_);
return v___x_732_;
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v_ctx_738_; lean_object* v___x_739_; lean_object* v_ctx_740_; lean_object* v_simpTheorems_741_; lean_object* v_fvarId_742_; lean_object* v_userName_743_; lean_object* v_id_744_; lean_object* v_origType_745_; lean_object* v_type_746_; lean_object* v_proof_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_mvarId_752_; lean_object* v_usedTheorems_753_; lean_object* v_diag_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec_ref(v_b_699_);
v___x_733_ = lean_box(0);
v___x_734_ = lean_box(0);
v___x_735_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0));
v___x_736_ = lean_array_fget_borrowed(v___x_696_, v_a_698_);
v___x_737_ = lean_st_ref_get(v___y_700_);
v_ctx_738_ = lean_ctor_get(v___x_737_, 2);
lean_inc_ref(v_ctx_738_);
lean_dec(v___x_737_);
v___x_739_ = lean_st_ref_get(v___y_700_);
v_ctx_740_ = lean_ctor_get(v___x_739_, 2);
lean_inc_ref(v_ctx_740_);
lean_dec(v___x_739_);
v_simpTheorems_741_ = lean_ctor_get(v_ctx_740_, 6);
lean_inc_ref(v_simpTheorems_741_);
lean_dec_ref(v_ctx_740_);
v_fvarId_742_ = lean_ctor_get(v___x_736_, 0);
v_userName_743_ = lean_ctor_get(v___x_736_, 1);
v_id_744_ = lean_ctor_get(v___x_736_, 2);
v_origType_745_ = lean_ctor_get(v___x_736_, 3);
v_type_746_ = lean_ctor_get(v___x_736_, 4);
v_proof_747_ = lean_ctor_get(v___x_736_, 5);
lean_inc_ref(v_id_744_);
v___x_748_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(v_simpTheorems_741_, v_id_744_);
v___x_749_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v_ctx_738_, v___x_748_);
v___x_750_ = lean_st_ref_get(v___y_700_);
v___x_751_ = lean_st_ref_get(v___y_700_);
v_mvarId_752_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_mvarId_752_);
lean_dec(v___x_750_);
v_usedTheorems_753_ = lean_ctor_get(v___x_751_, 4);
lean_inc_ref(v_usedTheorems_753_);
v_diag_754_ = lean_ctor_get(v___x_751_, 5);
lean_inc_ref(v_diag_754_);
lean_dec(v___x_751_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_usedTheorems_753_);
lean_ctor_set(v___x_755_, 1, v_diag_754_);
lean_inc_ref(v___x_697_);
lean_inc_ref(v___x_749_);
lean_inc_ref(v_type_746_);
lean_inc_ref(v_proof_747_);
v___x_756_ = l_Lean_Meta_simpStep(v_mvarId_752_, v_proof_747_, v_type_746_, v___x_749_, v___x_697_, v___x_734_, v___x_731_, v___x_755_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec_ref_known(v___x_755_, 2);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_849_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_849_ == 0)
{
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_849_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_849_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_fst_761_; lean_object* v_snd_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_848_; 
v_fst_761_ = lean_ctor_get(v_a_757_, 0);
v_snd_762_ = lean_ctor_get(v_a_757_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_a_757_);
if (v_isSharedCheck_848_ == 0)
{
v___x_764_ = v_a_757_;
v_isShared_765_ = v_isSharedCheck_848_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_snd_762_);
lean_inc(v_fst_761_);
lean_dec(v_a_757_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_848_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; uint8_t v_modified_767_; lean_object* v_mvarId_768_; lean_object* v_entries_769_; lean_object* v_ctx_770_; lean_object* v_simprocs_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_845_; 
v___x_766_ = lean_st_ref_take(v___y_700_);
v_modified_767_ = lean_ctor_get_uint8(v___x_766_, sizeof(void*)*6);
v_mvarId_768_ = lean_ctor_get(v___x_766_, 0);
v_entries_769_ = lean_ctor_get(v___x_766_, 1);
v_ctx_770_ = lean_ctor_get(v___x_766_, 2);
v_simprocs_771_ = lean_ctor_get(v___x_766_, 3);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; lean_object* v_unused_847_; 
v_unused_846_ = lean_ctor_get(v___x_766_, 5);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v___x_766_, 4);
lean_dec(v_unused_847_);
v___x_773_ = v___x_766_;
v_isShared_774_ = v_isSharedCheck_845_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_simprocs_771_);
lean_inc(v_ctx_770_);
lean_inc(v_entries_769_);
lean_inc(v_mvarId_768_);
lean_dec(v___x_766_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_845_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_usedTheorems_775_; lean_object* v_diag_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_844_; 
v_usedTheorems_775_ = lean_ctor_get(v_snd_762_, 0);
v_diag_776_ = lean_ctor_get(v_snd_762_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_snd_762_);
if (v_isSharedCheck_844_ == 0)
{
v___x_778_ = v_snd_762_;
v_isShared_779_ = v_isSharedCheck_844_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_diag_776_);
lean_inc(v_usedTheorems_775_);
lean_dec(v_snd_762_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_844_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 5, v_diag_776_);
lean_ctor_set(v___x_773_, 4, v_usedTheorems_775_);
v___x_781_ = v___x_773_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_mvarId_768_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_entries_769_);
lean_ctor_set(v_reuseFailAlloc_843_, 2, v_ctx_770_);
lean_ctor_set(v_reuseFailAlloc_843_, 3, v_simprocs_771_);
lean_ctor_set(v_reuseFailAlloc_843_, 4, v_usedTheorems_775_);
lean_ctor_set(v_reuseFailAlloc_843_, 5, v_diag_776_);
lean_ctor_set_uint8(v_reuseFailAlloc_843_, sizeof(void*)*6, v_modified_767_);
v___x_781_ = v_reuseFailAlloc_843_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; 
v___x_782_ = lean_st_ref_put(v___y_700_, v___x_781_);
if (lean_obj_tag(v_fst_761_) == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
lean_del_object(v___x_778_);
lean_dec_ref(v___x_749_);
lean_dec(v_a_698_);
lean_dec_ref(v___x_697_);
v___x_783_ = lean_box(v___x_731_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 1, v___x_733_);
lean_ctor_set(v___x_764_, 0, v___x_784_);
v___x_786_ = v___x_764_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_733_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_786_);
v___x_788_ = v___x_759_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
lean_object* v_val_791_; lean_object* v_fst_792_; lean_object* v_snd_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_842_; 
lean_del_object(v___x_764_);
lean_del_object(v___x_759_);
v_val_791_ = lean_ctor_get(v_fst_761_, 0);
lean_inc(v_val_791_);
lean_dec_ref_known(v_fst_761_, 1);
v_fst_792_ = lean_ctor_get(v_val_791_, 0);
v_snd_793_ = lean_ctor_get(v_val_791_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v_val_791_);
if (v_isSharedCheck_842_ == 0)
{
v___x_795_ = v_val_791_;
v_isShared_796_ = v_isSharedCheck_842_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snd_793_);
lean_inc(v_fst_792_);
lean_dec(v_val_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_842_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
uint8_t v___x_797_; 
v___x_797_ = lean_expr_eqv(v_snd_793_, v_type_746_);
if (v___x_797_ == 0)
{
lean_object* v_toCold_798_; lean_object* v_options_799_; lean_object* v_inheritedTraceOptions_800_; uint8_t v_hasTrace_801_; 
v_toCold_798_ = lean_ctor_get(v___y_703_, 0);
v_options_799_ = lean_ctor_get(v_toCold_798_, 2);
v_inheritedTraceOptions_800_ = lean_ctor_get(v_toCold_798_, 11);
v_hasTrace_801_ = lean_ctor_get_uint8(v_options_799_, sizeof(void*)*1);
if (v_hasTrace_801_ == 0)
{
lean_del_object(v___x_795_);
lean_del_object(v___x_778_);
goto v___jp_802_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_804_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_805_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8);
v___x_806_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_800_, v_options_799_, v___x_805_);
if (v___x_806_ == 0)
{
lean_del_object(v___x_795_);
lean_del_object(v___x_778_);
goto v___jp_802_;
}
else
{
lean_object* v___x_807_; 
lean_inc_ref(v_id_744_);
v___x_807_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_id_744_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v___x_809_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10);
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 7);
lean_ctor_set(v___x_795_, 1, v_a_808_);
lean_ctor_set(v___x_795_, 0, v___x_809_);
v___x_811_ = v___x_795_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_a_808_);
v___x_811_ = v_reuseFailAlloc_833_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12);
if (v_isShared_779_ == 0)
{
lean_ctor_set_tag(v___x_778_, 7);
lean_ctor_set(v___x_778_, 1, v___x_812_);
lean_ctor_set(v___x_778_, 0, v___x_811_);
v___x_814_ = v___x_778_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___x_812_);
v___x_814_ = v_reuseFailAlloc_832_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
lean_inc_ref(v_type_746_);
v___x_815_ = l_Lean_MessageData_ofExpr(v_type_746_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
lean_inc(v_snd_793_);
v___x_819_ = l_Lean_MessageData_ofExpr(v_snd_793_);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v___x_804_, v___x_820_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
lean_inc_ref(v_origType_745_);
lean_inc(v_userName_743_);
lean_inc(v_fvarId_742_);
v___x_823_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fvarId_742_, v_fst_792_, v_snd_793_, v___x_749_, v___x_731_, v___x_735_, v_a_698_, v___x_733_, v_userName_743_, v_origType_745_, v_a_822_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
v___y_712_ = v___x_823_;
goto v___jp_711_;
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec(v_snd_793_);
lean_dec(v_fst_792_);
lean_dec_ref(v___x_749_);
lean_dec(v_a_698_);
lean_dec_ref(v___x_697_);
v_a_824_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_821_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_821_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_del_object(v___x_795_);
lean_dec(v_snd_793_);
lean_dec(v_fst_792_);
lean_del_object(v___x_778_);
lean_dec_ref(v___x_749_);
lean_dec(v_a_698_);
lean_dec_ref(v___x_697_);
v_a_834_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_807_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_807_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
v___jp_802_:
{
lean_object* v___x_803_; 
lean_inc_ref(v_origType_745_);
lean_inc(v_userName_743_);
lean_inc(v_fvarId_742_);
v___x_803_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fvarId_742_, v_fst_792_, v_snd_793_, v___x_749_, v___x_731_, v___x_735_, v_a_698_, v___x_733_, v_userName_743_, v_origType_745_, v___x_733_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
v___y_712_ = v___x_803_;
goto v___jp_711_;
}
}
else
{
lean_del_object(v___x_795_);
lean_dec(v_snd_793_);
lean_dec(v_fst_792_);
lean_del_object(v___x_778_);
lean_dec_ref(v___x_749_);
v_a_707_ = v___x_735_;
goto v___jp_706_;
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
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec_ref(v___x_749_);
lean_dec(v_a_698_);
lean_dec_ref(v___x_697_);
v_a_850_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_756_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_756_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
v___jp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_nat_add(v_a_698_, v___x_708_);
lean_dec(v_a_698_);
v_a_698_ = v___x_709_;
v_b_699_ = v_a_707_;
goto _start;
}
v___jp_711_:
{
if (lean_obj_tag(v___y_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_722_; 
v_a_713_ = lean_ctor_get(v___y_712_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___y_712_);
if (v_isSharedCheck_722_ == 0)
{
v___x_715_ = v___y_712_;
v_isShared_716_ = v_isSharedCheck_722_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___y_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_722_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
if (lean_obj_tag(v_a_713_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; 
lean_dec(v_a_698_);
lean_dec_ref(v___x_697_);
v_a_717_ = lean_ctor_get(v_a_713_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v_a_713_, 1);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v_a_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
else
{
lean_object* v_a_721_; 
lean_del_object(v___x_715_);
v_a_721_ = lean_ctor_get(v_a_713_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v_a_713_, 1);
v_a_707_ = v_a_721_;
goto v___jp_706_;
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_a_698_);
lean_dec_ref(v___x_697_);
v_a_723_ = lean_ctor_get(v___y_712_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___y_712_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___y_712_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___y_712_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___boxed(lean_object* v_upperBound_858_, lean_object* v___x_859_, lean_object* v___x_860_, lean_object* v_a_861_, lean_object* v_b_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_upperBound_858_, v___x_859_, v___x_860_, v_a_861_, v_b_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___x_859_);
lean_dec(v_upperBound_858_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___x_887_; lean_object* v_mvarId_888_; lean_object* v_entries_889_; lean_object* v_ctx_890_; lean_object* v_simprocs_891_; lean_object* v_usedTheorems_892_; lean_object* v_diag_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_1000_; 
v___x_887_ = lean_st_ref_take(v_a_870_);
v_mvarId_888_ = lean_ctor_get(v___x_887_, 0);
v_entries_889_ = lean_ctor_get(v___x_887_, 1);
v_ctx_890_ = lean_ctor_get(v___x_887_, 2);
v_simprocs_891_ = lean_ctor_get(v___x_887_, 3);
v_usedTheorems_892_ = lean_ctor_get(v___x_887_, 4);
v_diag_893_ = lean_ctor_get(v___x_887_, 5);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_895_ = v___x_887_;
v_isShared_896_ = v_isSharedCheck_1000_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_diag_893_);
lean_inc(v_usedTheorems_892_);
lean_inc(v_simprocs_891_);
lean_inc(v_ctx_890_);
lean_inc(v_entries_889_);
lean_inc(v_mvarId_888_);
lean_dec(v___x_887_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_1000_;
goto v_resetjp_894_;
}
v___jp_876_:
{
lean_object* v___x_882_; uint8_t v_modified_883_; 
v___x_882_ = lean_st_ref_get(v___y_877_);
v_modified_883_ = lean_ctor_get_uint8(v___x_882_, sizeof(void*)*6);
lean_dec(v___x_882_);
if (v_modified_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_box(v_modified_883_);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
return v___x_885_;
}
else
{
v_a_870_ = v___y_877_;
v_a_871_ = v___y_878_;
v_a_872_ = v___y_879_;
v_a_873_ = v___y_880_;
v_a_874_ = v___y_881_;
goto _start;
}
}
v_resetjp_894_:
{
uint8_t v___x_897_; lean_object* v___x_899_; 
v___x_897_ = 0;
if (v_isShared_896_ == 0)
{
v___x_899_ = v___x_895_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_mvarId_888_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_entries_889_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_ctx_890_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_simprocs_891_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v_usedTheorems_892_);
lean_ctor_set(v_reuseFailAlloc_999_, 5, v_diag_893_);
v___x_899_ = v_reuseFailAlloc_999_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_simprocs_902_; lean_object* v___x_903_; lean_object* v_entries_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
lean_ctor_set_uint8(v___x_899_, sizeof(void*)*6, v___x_897_);
v___x_900_ = lean_st_ref_put(v_a_870_, v___x_899_);
v___x_901_ = lean_st_ref_get(v_a_870_);
v_simprocs_902_ = lean_ctor_get(v___x_901_, 3);
lean_inc_ref_n(v_simprocs_902_, 2);
lean_dec(v___x_901_);
v___x_903_ = lean_st_ref_get(v_a_870_);
v_entries_904_ = lean_ctor_get(v___x_903_, 1);
lean_inc_ref(v_entries_904_);
lean_dec(v___x_903_);
v___x_905_ = lean_array_get_size(v_entries_904_);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_box(0);
v___x_908_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0));
v___x_909_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v___x_905_, v_entries_904_, v_simprocs_902_, v___x_906_, v___x_908_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
lean_dec_ref(v_entries_904_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_990_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_990_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_990_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_990_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_fst_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_988_; 
v_fst_914_ = lean_ctor_get(v_a_910_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v_a_910_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v_a_910_, 1);
lean_dec(v_unused_989_);
v___x_916_ = v_a_910_;
v_isShared_917_ = v_isSharedCheck_988_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_fst_914_);
lean_dec(v_a_910_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_988_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
if (lean_obj_tag(v_fst_914_) == 0)
{
lean_object* v___x_918_; lean_object* v_mvarId_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_ctx_922_; lean_object* v_usedTheorems_923_; lean_object* v_diag_924_; uint8_t v___x_925_; lean_object* v___x_927_; 
lean_del_object(v___x_912_);
v___x_918_ = lean_st_ref_get(v_a_870_);
v_mvarId_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_mvarId_919_);
lean_dec(v___x_918_);
v___x_920_ = lean_st_ref_get(v_a_870_);
v___x_921_ = lean_st_ref_get(v_a_870_);
v_ctx_922_ = lean_ctor_get(v___x_920_, 2);
lean_inc_ref(v_ctx_922_);
lean_dec(v___x_920_);
v_usedTheorems_923_ = lean_ctor_get(v___x_921_, 4);
lean_inc_ref(v_usedTheorems_923_);
v_diag_924_ = lean_ctor_get(v___x_921_, 5);
lean_inc_ref(v_diag_924_);
lean_dec(v___x_921_);
v___x_925_ = 1;
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 1, v_diag_924_);
lean_ctor_set(v___x_916_, 0, v_usedTheorems_923_);
v___x_927_ = v___x_916_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_usedTheorems_923_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_diag_924_);
v___x_927_ = v_reuseFailAlloc_983_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; 
lean_inc(v_mvarId_919_);
v___x_928_ = l_Lean_Meta_simpTarget(v_mvarId_919_, v_ctx_922_, v_simprocs_902_, v___x_907_, v___x_925_, v___x_927_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_974_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_974_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_974_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_974_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_fst_933_; lean_object* v_snd_934_; lean_object* v___x_935_; uint8_t v_modified_936_; lean_object* v_mvarId_937_; lean_object* v_entries_938_; lean_object* v_ctx_939_; lean_object* v_simprocs_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_971_; 
v_fst_933_ = lean_ctor_get(v_a_929_, 0);
lean_inc(v_fst_933_);
v_snd_934_ = lean_ctor_get(v_a_929_, 1);
lean_inc(v_snd_934_);
lean_dec(v_a_929_);
v___x_935_ = lean_st_ref_take(v_a_870_);
v_modified_936_ = lean_ctor_get_uint8(v___x_935_, sizeof(void*)*6);
v_mvarId_937_ = lean_ctor_get(v___x_935_, 0);
v_entries_938_ = lean_ctor_get(v___x_935_, 1);
v_ctx_939_ = lean_ctor_get(v___x_935_, 2);
v_simprocs_940_ = lean_ctor_get(v___x_935_, 3);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; lean_object* v_unused_973_; 
v_unused_972_ = lean_ctor_get(v___x_935_, 5);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v___x_935_, 4);
lean_dec(v_unused_973_);
v___x_942_ = v___x_935_;
v_isShared_943_ = v_isSharedCheck_971_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_simprocs_940_);
lean_inc(v_ctx_939_);
lean_inc(v_entries_938_);
lean_inc(v_mvarId_937_);
lean_dec(v___x_935_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_971_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_usedTheorems_944_; lean_object* v_diag_945_; lean_object* v___x_947_; 
v_usedTheorems_944_ = lean_ctor_get(v_snd_934_, 0);
lean_inc_ref(v_usedTheorems_944_);
v_diag_945_ = lean_ctor_get(v_snd_934_, 1);
lean_inc_ref(v_diag_945_);
lean_dec(v_snd_934_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 5, v_diag_945_);
lean_ctor_set(v___x_942_, 4, v_usedTheorems_944_);
v___x_947_ = v___x_942_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_mvarId_937_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_entries_938_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_ctx_939_);
lean_ctor_set(v_reuseFailAlloc_970_, 3, v_simprocs_940_);
lean_ctor_set(v_reuseFailAlloc_970_, 4, v_usedTheorems_944_);
lean_ctor_set(v_reuseFailAlloc_970_, 5, v_diag_945_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*6, v_modified_936_);
v___x_947_ = v_reuseFailAlloc_970_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; 
v___x_948_ = lean_st_ref_put(v_a_870_, v___x_947_);
if (lean_obj_tag(v_fst_933_) == 0)
{
lean_object* v___x_949_; lean_object* v___x_951_; 
lean_dec(v_mvarId_919_);
v___x_949_ = lean_box(v___x_925_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_949_);
v___x_951_ = v___x_931_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
else
{
lean_object* v_val_953_; uint8_t v___x_954_; 
lean_del_object(v___x_931_);
v_val_953_ = lean_ctor_get(v_fst_933_, 0);
lean_inc(v_val_953_);
lean_dec_ref_known(v_fst_933_, 1);
v___x_954_ = l_Lean_instBEqMVarId_beq(v_mvarId_919_, v_val_953_);
lean_dec(v_mvarId_919_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v_entries_956_; lean_object* v_ctx_957_; lean_object* v_simprocs_958_; lean_object* v_usedTheorems_959_; lean_object* v_diag_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_968_; 
v___x_955_ = lean_st_ref_take(v_a_870_);
v_entries_956_ = lean_ctor_get(v___x_955_, 1);
v_ctx_957_ = lean_ctor_get(v___x_955_, 2);
v_simprocs_958_ = lean_ctor_get(v___x_955_, 3);
v_usedTheorems_959_ = lean_ctor_get(v___x_955_, 4);
v_diag_960_ = lean_ctor_get(v___x_955_, 5);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v___x_955_, 0);
lean_dec(v_unused_969_);
v___x_962_ = v___x_955_;
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_diag_960_);
lean_inc(v_usedTheorems_959_);
lean_inc(v_simprocs_958_);
lean_inc(v_ctx_957_);
lean_inc(v_entries_956_);
lean_dec(v___x_955_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v_val_953_);
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_val_953_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_entries_956_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_ctx_957_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_simprocs_958_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_usedTheorems_959_);
lean_ctor_set(v_reuseFailAlloc_967_, 5, v_diag_960_);
v___x_965_ = v_reuseFailAlloc_967_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; 
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*6, v___x_925_);
v___x_966_ = lean_st_ref_put(v_a_870_, v___x_965_);
v___y_877_ = v_a_870_;
v___y_878_ = v_a_871_;
v___y_879_ = v_a_872_;
v___y_880_ = v_a_873_;
v___y_881_ = v_a_874_;
goto v___jp_876_;
}
}
}
else
{
lean_dec(v_val_953_);
v___y_877_ = v_a_870_;
v___y_878_ = v_a_871_;
v___y_879_ = v_a_872_;
v___y_880_ = v_a_873_;
v___y_881_ = v_a_874_;
goto v___jp_876_;
}
}
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_mvarId_919_);
v_a_975_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_928_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_928_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
else
{
lean_object* v_val_984_; lean_object* v___x_986_; 
lean_del_object(v___x_916_);
lean_dec_ref(v_simprocs_902_);
v_val_984_ = lean_ctor_get(v_fst_914_, 0);
lean_inc(v_val_984_);
lean_dec_ref_known(v_fst_914_, 1);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v_val_984_);
v___x_986_ = v___x_912_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_val_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref(v_simprocs_902_);
v_a_991_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_909_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_909_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___boxed(lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(lean_object* v_cls_1008_, lean_object* v_msg_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_cls_1008_, v_msg_1009_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___boxed(lean_object* v_cls_1017_, lean_object* v_msg_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(v_cls_1017_, v_msg_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(lean_object* v_upperBound_1026_, lean_object* v___x_1027_, lean_object* v___x_1028_, lean_object* v_inst_1029_, lean_object* v_R_1030_, lean_object* v_a_1031_, lean_object* v_b_1032_, lean_object* v_c_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_upperBound_1026_, v___x_1027_, v___x_1028_, v_a_1031_, v_b_1032_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___boxed(lean_object* v_upperBound_1041_, lean_object* v___x_1042_, lean_object* v___x_1043_, lean_object* v_inst_1044_, lean_object* v_R_1045_, lean_object* v_a_1046_, lean_object* v_b_1047_, lean_object* v_c_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(v_upperBound_1041_, v___x_1042_, v___x_1043_, v_inst_1044_, v_R_1045_, v_a_1046_, v_b_1047_, v_c_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___x_1042_);
lean_dec(v_upperBound_1041_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(lean_object* v_as_1056_, size_t v_sz_1057_, size_t v_i_1058_, lean_object* v_b_1059_){
_start:
{
lean_object* v_a_1062_; uint8_t v___x_1066_; 
v___x_1066_ = lean_usize_dec_lt(v_i_1058_, v_sz_1057_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v_b_1059_);
return v___x_1067_;
}
else
{
lean_object* v_snd_1068_; lean_object* v_fst_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1106_; 
v_snd_1068_ = lean_ctor_get(v_b_1059_, 1);
v_fst_1069_ = lean_ctor_get(v_b_1059_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_b_1059_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1071_ = v_b_1059_;
v_isShared_1072_ = v_isSharedCheck_1106_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_snd_1068_);
lean_inc(v_fst_1069_);
lean_dec(v_b_1059_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1106_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_fst_1073_; lean_object* v_snd_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1105_; 
v_fst_1073_ = lean_ctor_get(v_snd_1068_, 0);
v_snd_1074_ = lean_ctor_get(v_snd_1068_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_snd_1068_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1076_ = v_snd_1068_;
v_isShared_1077_ = v_isSharedCheck_1105_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_snd_1074_);
lean_inc(v_fst_1073_);
lean_dec(v_snd_1068_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1105_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v_a_1078_; lean_object* v_fvarId_1079_; lean_object* v_userName_1080_; lean_object* v_origType_1081_; lean_object* v_type_1082_; lean_object* v_proof_1083_; uint8_t v___x_1097_; 
v_a_1078_ = lean_array_uget_borrowed(v_as_1056_, v_i_1058_);
v_fvarId_1079_ = lean_ctor_get(v_a_1078_, 0);
v_userName_1080_ = lean_ctor_get(v_a_1078_, 1);
v_origType_1081_ = lean_ctor_get(v_a_1078_, 3);
v_type_1082_ = lean_ctor_get(v_a_1078_, 4);
v_proof_1083_ = lean_ctor_get(v_a_1078_, 5);
lean_inc_ref(v_type_1082_);
v___x_1097_ = l_Lean_Expr_isTrue(v_type_1082_);
if (v___x_1097_ == 0)
{
uint8_t v___x_1098_; 
v___x_1098_ = lean_unbox(v_snd_1074_);
if (v___x_1098_ == 0)
{
uint8_t v___x_1099_; 
v___x_1099_ = lean_expr_eqv(v_type_1082_, v_origType_1081_);
if (v___x_1099_ == 0)
{
lean_dec(v_snd_1074_);
goto v___jp_1084_;
}
else
{
if (v___x_1097_ == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_del_object(v___x_1076_);
lean_del_object(v___x_1071_);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v_fst_1073_);
lean_ctor_set(v___x_1100_, 1, v_snd_1074_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v_fst_1069_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v_a_1062_ = v___x_1101_;
goto v___jp_1061_;
}
else
{
lean_dec(v_snd_1074_);
goto v___jp_1084_;
}
}
}
else
{
lean_dec(v_snd_1074_);
goto v___jp_1084_;
}
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_del_object(v___x_1076_);
lean_del_object(v___x_1071_);
lean_inc(v_fvarId_1079_);
v___x_1102_ = lean_array_push(v_fst_1073_, v_fvarId_1079_);
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v_snd_1074_);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v_fst_1069_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v_a_1062_ = v___x_1104_;
goto v___jp_1061_;
}
v___jp_1084_:
{
lean_object* v___x_1085_; uint8_t v___x_1086_; uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
lean_inc(v_fvarId_1079_);
v___x_1085_ = lean_array_push(v_fst_1073_, v_fvarId_1079_);
v___x_1086_ = 0;
v___x_1087_ = 0;
lean_inc_ref(v_proof_1083_);
lean_inc_ref(v_type_1082_);
lean_inc(v_userName_1080_);
v___x_1088_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1088_, 0, v_userName_1080_);
lean_ctor_set(v___x_1088_, 1, v_type_1082_);
lean_ctor_set(v___x_1088_, 2, v_proof_1083_);
lean_ctor_set_uint8(v___x_1088_, sizeof(void*)*3, v___x_1086_);
lean_ctor_set_uint8(v___x_1088_, sizeof(void*)*3 + 1, v___x_1087_);
v___x_1089_ = lean_array_push(v_fst_1069_, v___x_1088_);
v___x_1090_ = lean_box(v___x_1066_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v___x_1090_);
lean_ctor_set(v___x_1076_, 0, v___x_1085_);
v___x_1092_ = v___x_1076_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1094_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v___x_1092_);
lean_ctor_set(v___x_1071_, 0, v___x_1089_);
v___x_1094_ = v___x_1071_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
v_a_1062_ = v___x_1094_;
goto v___jp_1061_;
}
}
}
}
}
}
v___jp_1061_:
{
size_t v___x_1063_; size_t v___x_1064_; 
v___x_1063_ = ((size_t)1ULL);
v___x_1064_ = lean_usize_add(v_i_1058_, v___x_1063_);
v_i_1058_ = v___x_1064_;
v_b_1059_ = v_a_1062_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg___boxed(lean_object* v_as_1107_, lean_object* v_sz_1108_, lean_object* v_i_1109_, lean_object* v_b_1110_, lean_object* v___y_1111_){
_start:
{
size_t v_sz_boxed_1112_; size_t v_i_boxed_1113_; lean_object* v_res_1114_; 
v_sz_boxed_1112_ = lean_unbox_usize(v_sz_1108_);
lean_dec(v_sz_1108_);
v_i_boxed_1113_ = lean_unbox_usize(v_i_1109_);
lean_dec(v_i_1109_);
v_res_1114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_as_1107_, v_sz_boxed_1112_, v_i_boxed_1113_, v_b_1110_);
lean_dec_ref(v_as_1107_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_main(lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v___x_1124_; 
lean_dec_ref_known(v___x_1123_, 1);
v___x_1124_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1185_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1185_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1185_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
uint8_t v___x_1129_; 
v___x_1129_ = lean_unbox(v_a_1125_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v_mvarId_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_entries_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; size_t v_sz_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
lean_del_object(v___x_1127_);
v___x_1130_ = lean_st_ref_get(v_a_1117_);
v_mvarId_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_mvarId_1131_);
lean_dec(v___x_1130_);
v___x_1132_ = ((lean_object*)(l_Lean_Meta_SimpAll_main___closed__0));
v___x_1133_ = lean_st_ref_get(v_a_1117_);
v_entries_1134_ = lean_ctor_get(v___x_1133_, 1);
lean_inc_ref(v_entries_1134_);
lean_dec(v___x_1133_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1132_);
lean_ctor_set(v___x_1135_, 1, v_a_1125_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1132_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v_sz_1137_ = lean_array_size(v_entries_1134_);
v___x_1138_ = ((size_t)0ULL);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_entries_1134_, v_sz_1137_, v___x_1138_, v___x_1136_);
lean_dec_ref(v_entries_1134_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v_snd_1141_; lean_object* v_fst_1142_; lean_object* v_fst_1143_; lean_object* v___x_1144_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v_snd_1141_ = lean_ctor_get(v_a_1140_, 1);
lean_inc(v_snd_1141_);
v_fst_1142_ = lean_ctor_get(v_a_1140_, 0);
lean_inc(v_fst_1142_);
lean_dec(v_a_1140_);
v_fst_1143_ = lean_ctor_get(v_snd_1141_, 0);
lean_inc(v_fst_1143_);
lean_dec(v_snd_1141_);
v___x_1144_ = l_Lean_MVarId_assertHypotheses(v_mvarId_1131_, v_fst_1142_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v_snd_1146_; lean_object* v___x_1147_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v_snd_1146_ = lean_ctor_get(v_a_1145_, 1);
lean_inc(v_snd_1146_);
lean_dec(v_a_1145_);
v___x_1147_ = l_Lean_MVarId_tryClearMany(v_snd_1146_, v_fst_1143_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v_fst_1143_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1156_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_a_1148_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1152_);
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_a_1157_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1147_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1147_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v_fst_1143_);
v_a_1165_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1144_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1144_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec(v_mvarId_1131_);
v_a_1173_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1139_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1139_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
lean_dec(v_a_1125_);
v___x_1181_ = lean_box(0);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1181_);
v___x_1183_ = v___x_1127_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_a_1186_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1124_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1124_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
v_a_1194_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1123_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1123_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_main___boxed(lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Meta_SimpAll_main(v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(lean_object* v_as_1209_, size_t v_sz_1210_, size_t v_i_1211_, lean_object* v_b_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_as_1209_, v_sz_1210_, v_i_1211_, v_b_1212_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___boxed(lean_object* v_as_1220_, lean_object* v_sz_1221_, lean_object* v_i_1222_, lean_object* v_b_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
size_t v_sz_boxed_1230_; size_t v_i_boxed_1231_; lean_object* v_res_1232_; 
v_sz_boxed_1230_ = lean_unbox_usize(v_sz_1221_);
lean_dec(v_sz_1221_);
v_i_boxed_1231_ = lean_unbox_usize(v_i_1222_);
lean_dec(v_i_1222_);
v_res_1232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(v_as_1220_, v_sz_boxed_1230_, v_i_boxed_1231_, v_b_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v_as_1220_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(lean_object* v_mvarId_1233_, lean_object* v_x_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1233_, v_x_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
v_a_1249_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1240_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1240_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg___boxed(lean_object* v_mvarId_1257_, lean_object* v_x_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1257_, v_x_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(lean_object* v_00_u03b1_1265_, lean_object* v_mvarId_1266_, lean_object* v_x_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1266_, v_x_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___boxed(lean_object* v_00_u03b1_1274_, lean_object* v_mvarId_1275_, lean_object* v_x_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(v_00_u03b1_1274_, v_mvarId_1275_, v_x_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(lean_object* v_msg_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_ref_1289_; lean_object* v___x_1290_; lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1299_; 
v_ref_1289_ = lean_ctor_get(v___y_1286_, 2);
v___x_1290_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msg_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
lean_inc(v_ref_1289_);
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_ref_1289_);
lean_ctor_set(v___x_1295_, 1, v_a_1291_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set_tag(v___x_1293_, 1);
lean_ctor_set(v___x_1293_, 0, v___x_1295_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg___boxed(lean_object* v_msg_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v_msg_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1306_;
}
}
static lean_object* _init_l_Lean_Meta_simpAll___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Lean_Meta_simpAll___lam__0___closed__0));
v___x_1309_ = l_Lean_stringToMessageData(v___x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___lam__0(lean_object* v___x_1310_, lean_object* v_ctx_1311_, lean_object* v_mvarId_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_st_mk_ref(v___x_1310_);
v___x_1319_ = l_Lean_Meta_SimpAll_main(v___x_1318_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1347_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1347_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1347_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_st_ref_get(v___x_1318_);
lean_dec(v___x_1318_);
if (lean_obj_tag(v_a_1320_) == 1)
{
lean_object* v_config_1333_; uint8_t v_failIfUnchanged_1334_; 
v_config_1333_ = lean_ctor_get(v_ctx_1311_, 0);
v_failIfUnchanged_1334_ = lean_ctor_get_uint8(v_config_1333_, sizeof(void*)*3 + 13);
if (v_failIfUnchanged_1334_ == 0)
{
goto v___jp_1325_;
}
else
{
lean_object* v_val_1335_; uint8_t v___x_1336_; 
v_val_1335_ = lean_ctor_get(v_a_1320_, 0);
v___x_1336_ = l_Lean_instBEqMVarId_beq(v_mvarId_1312_, v_val_1335_);
if (v___x_1336_ == 0)
{
goto v___jp_1325_;
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec_ref_known(v_a_1320_, 1);
lean_dec(v___x_1324_);
lean_del_object(v___x_1322_);
v___x_1337_ = lean_obj_once(&l_Lean_Meta_simpAll___lam__0___closed__1, &l_Lean_Meta_simpAll___lam__0___closed__1_once, _init_l_Lean_Meta_simpAll___lam__0___closed__1);
v___x_1338_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v___x_1337_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
else
{
goto v___jp_1325_;
}
v___jp_1325_:
{
lean_object* v_usedTheorems_1326_; lean_object* v_diag_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v_usedTheorems_1326_ = lean_ctor_get(v___x_1324_, 4);
lean_inc_ref(v_usedTheorems_1326_);
v_diag_1327_ = lean_ctor_get(v___x_1324_, 5);
lean_inc_ref(v_diag_1327_);
lean_dec(v___x_1324_);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v_usedTheorems_1326_);
lean_ctor_set(v___x_1328_, 1, v_diag_1327_);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v_a_1320_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1329_);
v___x_1331_ = v___x_1322_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec(v___x_1318_);
v_a_1348_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1319_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1319_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___lam__0___boxed(lean_object* v___x_1356_, lean_object* v_ctx_1357_, lean_object* v_mvarId_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Meta_simpAll___lam__0(v___x_1356_, v_ctx_1357_, v_mvarId_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v_mvarId_1358_);
lean_dec_ref(v_ctx_1357_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll(lean_object* v_mvarId_1367_, lean_object* v_ctx_1368_, lean_object* v_simprocs_1369_, lean_object* v_stats_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v_usedTheorems_1376_; lean_object* v_diag_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___f_1381_; lean_object* v___x_1382_; 
v_usedTheorems_1376_ = lean_ctor_get(v_stats_1370_, 0);
v_diag_1377_ = lean_ctor_get(v_stats_1370_, 1);
v___x_1378_ = 0;
v___x_1379_ = ((lean_object*)(l_Lean_Meta_simpAll___closed__0));
lean_inc_ref(v_diag_1377_);
lean_inc_ref(v_usedTheorems_1376_);
lean_inc_ref(v_ctx_1368_);
lean_inc_n(v_mvarId_1367_, 2);
v___x_1380_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1380_, 0, v_mvarId_1367_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
lean_ctor_set(v___x_1380_, 2, v_ctx_1368_);
lean_ctor_set(v___x_1380_, 3, v_simprocs_1369_);
lean_ctor_set(v___x_1380_, 4, v_usedTheorems_1376_);
lean_ctor_set(v___x_1380_, 5, v_diag_1377_);
lean_ctor_set_uint8(v___x_1380_, sizeof(void*)*6, v___x_1378_);
v___f_1381_ = lean_alloc_closure((void*)(l_Lean_Meta_simpAll___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1381_, 0, v___x_1380_);
lean_closure_set(v___f_1381_, 1, v_ctx_1368_);
lean_closure_set(v___f_1381_, 2, v_mvarId_1367_);
v___x_1382_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1367_, v___f_1381_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___boxed(lean_object* v_mvarId_1383_, lean_object* v_ctx_1384_, lean_object* v_simprocs_1385_, lean_object* v_stats_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Meta_simpAll(v_mvarId_1383_, v_ctx_1384_, v_simprocs_1385_, v_stats_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec_ref(v_stats_1386_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(lean_object* v_00_u03b1_1393_, lean_object* v_msg_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v_msg_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_msg_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(v_00_u03b1_1401_, v_msg_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1478_; uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1478_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_1479_ = 0;
v___x_1480_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_));
v___x_1481_ = l_Lean_registerTraceClass(v___x_1478_, v___x_1479_, v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2____boxed(lean_object* v_a_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_();
return v_res_1483_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_SimpAll(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
