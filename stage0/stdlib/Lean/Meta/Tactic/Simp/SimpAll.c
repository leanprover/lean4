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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheoremsArray_eraseTheorem(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__0_value;
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
v___x_96_ = lean_st_ref_set(v___y_77_, v___x_95_);
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
lean_object* v_a_188_; lean_object* v___x_189_; lean_object* v_ctx_190_; lean_object* v_indexConfig_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc_n(v_a_188_, 2);
lean_dec_ref(v___x_187_);
v___x_189_ = lean_st_ref_get(v___y_171_);
v_ctx_190_ = lean_ctor_get(v___x_189_, 2);
lean_inc_ref(v_ctx_190_);
lean_dec(v___x_189_);
v_indexConfig_191_ = lean_ctor_get(v_ctx_190_, 4);
lean_inc_ref(v_indexConfig_191_);
lean_dec_ref(v_ctx_190_);
v___x_192_ = l_Lean_LocalDecl_toExpr(v_a_188_);
lean_inc_ref(v___x_192_);
lean_inc_ref(v___x_185_);
v___x_193_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v_b_170_, v___x_185_, v___x_192_, v_indexConfig_191_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_195_; uint8_t v_modified_196_; lean_object* v_mvarId_197_; lean_object* v_entries_198_; lean_object* v_ctx_199_; lean_object* v_simprocs_200_; lean_object* v_usedTheorems_201_; lean_object* v_diag_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_242_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref(v___x_193_);
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
v___x_209_ = lean_st_ref_set(v___y_171_, v___x_208_);
v___x_210_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(v_a_166_, v_a_184_);
if (v___x_210_ == 0)
{
lean_dec_ref(v___x_192_);
lean_dec(v_a_188_);
lean_dec_ref(v___x_185_);
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
lean_dec_ref(v___x_212_);
v___x_214_ = l_Lean_LocalDecl_userName(v_a_188_);
lean_dec(v_a_188_);
lean_inc(v_a_184_);
v___x_215_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_215_, 0, v_a_184_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
lean_ctor_set(v___x_215_, 2, v___x_185_);
lean_ctor_set(v___x_215_, 3, v_a_213_);
lean_ctor_set(v___x_215_, 4, v_a_213_);
lean_ctor_set(v___x_215_, 5, v___x_192_);
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
v___x_230_ = lean_st_ref_set(v___y_171_, v___x_229_);
v_a_178_ = v_a_194_;
goto v___jp_177_;
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec(v_a_194_);
lean_dec_ref(v___x_192_);
lean_dec(v_a_188_);
lean_dec_ref(v___x_185_);
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
lean_dec_ref(v___x_192_);
lean_dec(v_a_188_);
lean_dec_ref(v___x_185_);
return v___x_193_;
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec_ref(v___x_185_);
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
lean_dec_ref(v___x_185_);
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
lean_object* v___x_272_; lean_object* v_mvarId_273_; lean_object* v___f_274_; lean_object* v___x_275_; 
v___x_272_ = lean_st_ref_get(v_a_266_);
v_mvarId_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_mvarId_273_);
lean_dec(v___x_272_);
v___f_274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___closed__0));
v___x_275_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_273_, v___f_274_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; lean_object* v_mvarId_278_; lean_object* v___x_279_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref(v___x_275_);
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
lean_dec_ref(v___x_279_);
v___x_281_ = lean_st_ref_get(v_a_266_);
v_ctx_282_ = lean_ctor_get(v___x_281_, 2);
lean_inc_ref(v_ctx_282_);
lean_dec(v___x_281_);
v_simpTheorems_283_ = lean_ctor_get(v_ctx_282_, 5);
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
v_simpTheorems_331_ = lean_ctor_get(v_ctx_330_, 5);
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
v_simpTheorems_344_ = lean_ctor_get(v_ctx_343_, 5);
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
lean_object* v___x_355_; lean_object* v_ngen_356_; lean_object* v_namePrefix_357_; lean_object* v_idx_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_387_; 
v___x_355_ = lean_st_ref_get(v___y_353_);
v_ngen_356_ = lean_ctor_get(v___x_355_, 2);
lean_inc_ref(v_ngen_356_);
lean_dec(v___x_355_);
v_namePrefix_357_ = lean_ctor_get(v_ngen_356_, 0);
v_idx_358_ = lean_ctor_get(v_ngen_356_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_ngen_356_);
if (v_isSharedCheck_387_ == 0)
{
v___x_360_ = v_ngen_356_;
v_isShared_361_ = v_isSharedCheck_387_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_idx_358_);
lean_inc(v_namePrefix_357_);
lean_dec(v_ngen_356_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_387_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v_env_363_; lean_object* v_nextMacroScope_364_; lean_object* v_auxDeclNGen_365_; lean_object* v_traceState_366_; lean_object* v_cache_367_; lean_object* v_messages_368_; lean_object* v_infoState_369_; lean_object* v_snapshotTasks_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_385_; 
v___x_362_ = lean_st_ref_take(v___y_353_);
v_env_363_ = lean_ctor_get(v___x_362_, 0);
v_nextMacroScope_364_ = lean_ctor_get(v___x_362_, 1);
v_auxDeclNGen_365_ = lean_ctor_get(v___x_362_, 3);
v_traceState_366_ = lean_ctor_get(v___x_362_, 4);
v_cache_367_ = lean_ctor_get(v___x_362_, 5);
v_messages_368_ = lean_ctor_get(v___x_362_, 6);
v_infoState_369_ = lean_ctor_get(v___x_362_, 7);
v_snapshotTasks_370_ = lean_ctor_get(v___x_362_, 8);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; 
v_unused_386_ = lean_ctor_get(v___x_362_, 2);
lean_dec(v_unused_386_);
v___x_372_ = v___x_362_;
v_isShared_373_ = v_isSharedCheck_385_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_snapshotTasks_370_);
lean_inc(v_infoState_369_);
lean_inc(v_messages_368_);
lean_inc(v_cache_367_);
lean_inc(v_traceState_366_);
lean_inc(v_auxDeclNGen_365_);
lean_inc(v_nextMacroScope_364_);
lean_inc(v_env_363_);
lean_dec(v___x_362_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_385_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v_r_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
lean_inc(v_idx_358_);
lean_inc(v_namePrefix_357_);
v_r_374_ = l_Lean_Name_num___override(v_namePrefix_357_, v_idx_358_);
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_add(v_idx_358_, v___x_375_);
lean_dec(v_idx_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_376_);
v___x_378_ = v___x_360_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_namePrefix_357_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___x_376_);
v___x_378_ = v_reuseFailAlloc_384_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 2, v___x_378_);
v___x_380_ = v___x_372_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_env_363_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_nextMacroScope_364_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v_auxDeclNGen_365_);
lean_ctor_set(v_reuseFailAlloc_383_, 4, v_traceState_366_);
lean_ctor_set(v_reuseFailAlloc_383_, 5, v_cache_367_);
lean_ctor_set(v_reuseFailAlloc_383_, 6, v_messages_368_);
lean_ctor_set(v_reuseFailAlloc_383_, 7, v_infoState_369_);
lean_ctor_set(v_reuseFailAlloc_383_, 8, v_snapshotTasks_370_);
v___x_380_ = v_reuseFailAlloc_383_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_st_ref_set(v___y_353_, v___x_380_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v_r_374_);
return v___x_382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg___boxed(lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_388_);
lean_dec(v___y_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0(lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_395_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___boxed(lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0(v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
return v_res_404_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0));
v___x_407_ = l_Lean_stringToMessageData(v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__2));
v___x_410_ = l_Lean_stringToMessageData(v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__4));
v___x_413_ = l_Lean_stringToMessageData(v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(lean_object* v_x_414_){
_start:
{
switch(lean_obj_tag(v_x_414_))
{
case 0:
{
lean_object* v_declName_416_; uint8_t v_post_417_; uint8_t v_inv_418_; uint8_t v___x_419_; lean_object* v_r_420_; 
v_declName_416_ = lean_ctor_get(v_x_414_, 0);
lean_inc(v_declName_416_);
v_post_417_ = lean_ctor_get_uint8(v_x_414_, sizeof(void*)*1);
v_inv_418_ = lean_ctor_get_uint8(v_x_414_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_414_);
v___x_419_ = 0;
v_r_420_ = l_Lean_MessageData_ofConstName(v_declName_416_, v___x_419_);
if (v_post_417_ == 0)
{
if (v_inv_418_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v_r_420_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v_r_420_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
else
{
if (v_inv_418_ == 0)
{
lean_object* v___x_427_; 
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v_r_420_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_r_420_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
}
case 1:
{
lean_object* v_fvarId_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_440_; 
v_fvarId_431_ = lean_ctor_get(v_x_414_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_440_ == 0)
{
v___x_433_ = v_x_414_;
v_isShared_434_ = v_isSharedCheck_440_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_fvarId_431_);
lean_dec(v_x_414_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_440_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_435_ = l_Lean_mkFVar(v_fvarId_431_);
v___x_436_ = l_Lean_MessageData_ofExpr(v___x_435_);
if (v_isShared_434_ == 0)
{
lean_ctor_set_tag(v___x_433_, 0);
lean_ctor_set(v___x_433_, 0, v___x_436_);
v___x_438_ = v___x_433_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
case 2:
{
lean_object* v_ref_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_ref_441_ = lean_ctor_get(v_x_414_, 1);
lean_inc(v_ref_441_);
lean_dec_ref(v_x_414_);
v___x_442_ = l_Lean_MessageData_ofSyntax(v_ref_441_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
default: 
{
lean_object* v_name_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_452_; 
v_name_444_ = lean_ctor_get(v_x_414_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_452_ == 0)
{
v___x_446_ = v_x_414_;
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_name_444_);
lean_dec(v_x_414_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = l_Lean_MessageData_ofName(v_name_444_);
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 0);
lean_ctor_set(v___x_446_, 0, v___x_448_);
v___x_450_ = v___x_446_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___boxed(lean_object* v_x_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_x_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1(lean_object* v_x_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_x_456_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___boxed(lean_object* v_x_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1(v_x_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(lean_object* v_msgData_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_478_; lean_object* v_env_479_; lean_object* v___x_480_; lean_object* v_mctx_481_; lean_object* v_lctx_482_; lean_object* v_options_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_478_ = lean_st_ref_get(v___y_476_);
v_env_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc_ref(v_env_479_);
lean_dec(v___x_478_);
v___x_480_ = lean_st_ref_get(v___y_474_);
v_mctx_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc_ref(v_mctx_481_);
lean_dec(v___x_480_);
v_lctx_482_ = lean_ctor_get(v___y_473_, 2);
v_options_483_ = lean_ctor_get(v___y_475_, 2);
lean_inc_ref(v_options_483_);
lean_inc_ref(v_lctx_482_);
v___x_484_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_484_, 0, v_env_479_);
lean_ctor_set(v___x_484_, 1, v_mctx_481_);
lean_ctor_set(v___x_484_, 2, v_lctx_482_);
lean_ctor_set(v___x_484_, 3, v_options_483_);
v___x_485_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_msgData_472_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2___boxed(lean_object* v_msgData_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msgData_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
return v_res_493_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_494_; double v___x_495_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_float_of_nat(v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(lean_object* v_cls_499_, lean_object* v_msg_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_ref_506_; lean_object* v___x_507_; lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_552_; 
v_ref_506_ = lean_ctor_get(v___y_503_, 5);
v___x_507_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msg_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_552_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_552_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_552_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v_traceState_513_; lean_object* v_env_514_; lean_object* v_nextMacroScope_515_; lean_object* v_ngen_516_; lean_object* v_auxDeclNGen_517_; lean_object* v_cache_518_; lean_object* v_messages_519_; lean_object* v_infoState_520_; lean_object* v_snapshotTasks_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_551_; 
v___x_512_ = lean_st_ref_take(v___y_504_);
v_traceState_513_ = lean_ctor_get(v___x_512_, 4);
v_env_514_ = lean_ctor_get(v___x_512_, 0);
v_nextMacroScope_515_ = lean_ctor_get(v___x_512_, 1);
v_ngen_516_ = lean_ctor_get(v___x_512_, 2);
v_auxDeclNGen_517_ = lean_ctor_get(v___x_512_, 3);
v_cache_518_ = lean_ctor_get(v___x_512_, 5);
v_messages_519_ = lean_ctor_get(v___x_512_, 6);
v_infoState_520_ = lean_ctor_get(v___x_512_, 7);
v_snapshotTasks_521_ = lean_ctor_get(v___x_512_, 8);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_551_ == 0)
{
v___x_523_ = v___x_512_;
v_isShared_524_ = v_isSharedCheck_551_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_snapshotTasks_521_);
lean_inc(v_infoState_520_);
lean_inc(v_messages_519_);
lean_inc(v_cache_518_);
lean_inc(v_traceState_513_);
lean_inc(v_auxDeclNGen_517_);
lean_inc(v_ngen_516_);
lean_inc(v_nextMacroScope_515_);
lean_inc(v_env_514_);
lean_dec(v___x_512_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_551_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
uint64_t v_tid_525_; lean_object* v_traces_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_550_; 
v_tid_525_ = lean_ctor_get_uint64(v_traceState_513_, sizeof(void*)*1);
v_traces_526_ = lean_ctor_get(v_traceState_513_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_traceState_513_);
if (v_isSharedCheck_550_ == 0)
{
v___x_528_ = v_traceState_513_;
v_isShared_529_ = v_isSharedCheck_550_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_traces_526_);
lean_dec(v_traceState_513_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_550_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; double v___x_531_; uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_530_ = lean_box(0);
v___x_531_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0);
v___x_532_ = 0;
v___x_533_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1));
v___x_534_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_534_, 0, v_cls_499_);
lean_ctor_set(v___x_534_, 1, v___x_530_);
lean_ctor_set(v___x_534_, 2, v___x_533_);
lean_ctor_set_float(v___x_534_, sizeof(void*)*3, v___x_531_);
lean_ctor_set_float(v___x_534_, sizeof(void*)*3 + 8, v___x_531_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*3 + 16, v___x_532_);
v___x_535_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2));
v___x_536_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v_a_508_);
lean_ctor_set(v___x_536_, 2, v___x_535_);
lean_inc(v_ref_506_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v_ref_506_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = l_Lean_PersistentArray_push___redArg(v_traces_526_, v___x_537_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_538_);
v___x_540_ = v___x_528_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_538_);
lean_ctor_set_uint64(v_reuseFailAlloc_549_, sizeof(void*)*1, v_tid_525_);
v___x_540_ = v_reuseFailAlloc_549_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 4, v___x_540_);
v___x_542_ = v___x_523_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_env_514_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_nextMacroScope_515_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_ngen_516_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_auxDeclNGen_517_);
lean_ctor_set(v_reuseFailAlloc_548_, 4, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_548_, 5, v_cache_518_);
lean_ctor_set(v_reuseFailAlloc_548_, 6, v_messages_519_);
lean_ctor_set(v_reuseFailAlloc_548_, 7, v_infoState_520_);
lean_ctor_set(v_reuseFailAlloc_548_, 8, v_snapshotTasks_521_);
v___x_542_ = v_reuseFailAlloc_548_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_543_ = lean_st_ref_set(v___y_504_, v___x_542_);
v___x_544_ = lean_box(0);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_544_);
v___x_546_ = v___x_510_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___boxed(lean_object* v_cls_553_, lean_object* v_msg_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_cls_553_, v_msg_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(lean_object* v_fst_561_, lean_object* v_snd_562_, lean_object* v___x_563_, lean_object* v_fvarId_564_, uint8_t v___x_565_, lean_object* v___x_566_, lean_object* v_a_567_, lean_object* v___x_568_, lean_object* v_userName_569_, lean_object* v_origType_570_, lean_object* v_____r_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_st_ref_get(v___y_572_);
v___x_579_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_576_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_581_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref(v___x_579_);
lean_inc_ref(v_snd_562_);
lean_inc_ref(v_fst_561_);
v___x_581_ = l_Lean_Meta_mkExpectedTypeHint(v_fst_561_, v_snd_562_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_ctx_582_; lean_object* v_a_583_; lean_object* v_simpTheorems_584_; lean_object* v_indexConfig_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_ctx_582_ = lean_ctor_get(v___x_578_, 2);
lean_inc_ref(v_ctx_582_);
lean_dec(v___x_578_);
v_a_583_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_583_);
lean_dec_ref(v___x_581_);
v_simpTheorems_584_ = lean_ctor_get(v_ctx_582_, 5);
lean_inc_ref(v_simpTheorems_584_);
lean_dec_ref(v_ctx_582_);
v_indexConfig_585_ = lean_ctor_get(v___x_563_, 4);
lean_inc(v_fvarId_564_);
v___x_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_586_, 0, v_fvarId_564_);
v___x_587_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(v_simpTheorems_584_, v___x_586_);
v___x_588_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_588_, 0, v_a_580_);
lean_inc_ref(v_indexConfig_585_);
lean_inc_ref(v___x_588_);
v___x_589_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v___x_587_, v___x_588_, v_a_583_, v_indexConfig_585_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_621_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_621_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_621_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_621_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v_mvarId_595_; lean_object* v_entries_596_; lean_object* v_simprocs_597_; lean_object* v_usedTheorems_598_; lean_object* v_diag_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_619_; 
v___x_594_ = lean_st_ref_take(v___y_572_);
v_mvarId_595_ = lean_ctor_get(v___x_594_, 0);
v_entries_596_ = lean_ctor_get(v___x_594_, 1);
v_simprocs_597_ = lean_ctor_get(v___x_594_, 3);
v_usedTheorems_598_ = lean_ctor_get(v___x_594_, 4);
v_diag_599_ = lean_ctor_get(v___x_594_, 5);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v___x_594_, 2);
lean_dec(v_unused_620_);
v___x_601_ = v___x_594_;
v_isShared_602_ = v_isSharedCheck_619_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_diag_599_);
lean_inc(v_usedTheorems_598_);
lean_inc(v_simprocs_597_);
lean_inc(v_entries_596_);
lean_inc(v_mvarId_595_);
lean_dec(v___x_594_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_619_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___y_604_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_array_get_size(v_entries_596_);
v___x_615_ = lean_nat_dec_lt(v_a_567_, v___x_614_);
if (v___x_615_ == 0)
{
lean_dec_ref(v___x_588_);
lean_dec_ref(v_origType_570_);
lean_dec(v_userName_569_);
lean_dec(v_fvarId_564_);
lean_dec_ref(v_snd_562_);
lean_dec_ref(v_fst_561_);
v___y_604_ = v_entries_596_;
goto v___jp_603_;
}
else
{
lean_object* v_xs_x27_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_xs_x27_616_ = lean_array_fset(v_entries_596_, v_a_567_, v___x_568_);
v___x_617_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_617_, 0, v_fvarId_564_);
lean_ctor_set(v___x_617_, 1, v_userName_569_);
lean_ctor_set(v___x_617_, 2, v___x_588_);
lean_ctor_set(v___x_617_, 3, v_origType_570_);
lean_ctor_set(v___x_617_, 4, v_snd_562_);
lean_ctor_set(v___x_617_, 5, v_fst_561_);
v___x_618_ = lean_array_fset(v_xs_x27_616_, v_a_567_, v___x_617_);
v___y_604_ = v___x_618_;
goto v___jp_603_;
}
v___jp_603_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v___x_563_, v_a_590_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 2, v___x_605_);
lean_ctor_set(v___x_601_, 1, v___y_604_);
v___x_607_ = v___x_601_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_mvarId_595_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___y_604_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_simprocs_597_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v_usedTheorems_598_);
lean_ctor_set(v_reuseFailAlloc_613_, 5, v_diag_599_);
v___x_607_ = v_reuseFailAlloc_613_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
lean_ctor_set_uint8(v___x_607_, sizeof(void*)*6, v___x_565_);
v___x_608_ = lean_st_ref_set(v___y_572_, v___x_607_);
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_566_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_609_);
v___x_611_ = v___x_592_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v___x_588_);
lean_dec_ref(v_origType_570_);
lean_dec(v_userName_569_);
lean_dec_ref(v___x_566_);
lean_dec(v_fvarId_564_);
lean_dec_ref(v___x_563_);
lean_dec_ref(v_snd_562_);
lean_dec_ref(v_fst_561_);
v_a_622_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_589_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_589_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v_a_580_);
lean_dec(v___x_578_);
lean_dec_ref(v_origType_570_);
lean_dec(v_userName_569_);
lean_dec_ref(v___x_566_);
lean_dec(v_fvarId_564_);
lean_dec_ref(v___x_563_);
lean_dec_ref(v_snd_562_);
lean_dec_ref(v_fst_561_);
v_a_630_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_581_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_581_);
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
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v___x_578_);
lean_dec_ref(v_origType_570_);
lean_dec(v_userName_569_);
lean_dec_ref(v___x_566_);
lean_dec(v_fvarId_564_);
lean_dec_ref(v___x_563_);
lean_dec_ref(v_snd_562_);
lean_dec_ref(v_fst_561_);
v_a_638_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_579_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_579_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_fst_646_ = _args[0];
lean_object* v_snd_647_ = _args[1];
lean_object* v___x_648_ = _args[2];
lean_object* v_fvarId_649_ = _args[3];
lean_object* v___x_650_ = _args[4];
lean_object* v___x_651_ = _args[5];
lean_object* v_a_652_ = _args[6];
lean_object* v___x_653_ = _args[7];
lean_object* v_userName_654_ = _args[8];
lean_object* v_origType_655_ = _args[9];
lean_object* v_____r_656_ = _args[10];
lean_object* v___y_657_ = _args[11];
lean_object* v___y_658_ = _args[12];
lean_object* v___y_659_ = _args[13];
lean_object* v___y_660_ = _args[14];
lean_object* v___y_661_ = _args[15];
lean_object* v___y_662_ = _args[16];
_start:
{
uint8_t v___x_27748__boxed_663_; lean_object* v_res_664_; 
v___x_27748__boxed_663_ = lean_unbox(v___x_650_);
v_res_664_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fst_646_, v_snd_647_, v___x_648_, v_fvarId_649_, v___x_27748__boxed_663_, v___x_651_, v_a_652_, v___x_653_, v_userName_654_, v_origType_655_, v_____r_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec(v_a_652_);
return v_res_664_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_681_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__7));
v___x_682_ = l_Lean_Name_append(v___x_681_, v___x_680_);
return v___x_682_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__9));
v___x_685_ = l_Lean_stringToMessageData(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__11));
v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__13));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(lean_object* v_upperBound_692_, lean_object* v___x_693_, lean_object* v___x_694_, lean_object* v_a_695_, lean_object* v_b_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_a_704_; lean_object* v___y_709_; uint8_t v___x_728_; 
v___x_728_ = lean_nat_dec_lt(v_a_695_, v_upperBound_692_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_dec(v_a_695_);
lean_dec_ref(v___x_694_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v_b_696_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_ctx_734_; lean_object* v_ctx_735_; lean_object* v_simpTheorems_736_; lean_object* v___x_737_; lean_object* v_fvarId_738_; lean_object* v_userName_739_; lean_object* v_id_740_; lean_object* v_origType_741_; lean_object* v_type_742_; lean_object* v_proof_743_; lean_object* v_mvarId_744_; lean_object* v_usedTheorems_745_; lean_object* v_diag_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec_ref(v_b_696_);
v___x_730_ = lean_st_ref_get(v___y_697_);
v___x_731_ = lean_st_ref_get(v___y_697_);
v___x_732_ = lean_st_ref_get(v___y_697_);
v___x_733_ = lean_st_ref_get(v___y_697_);
v_ctx_734_ = lean_ctor_get(v___x_731_, 2);
lean_inc_ref(v_ctx_734_);
lean_dec(v___x_731_);
v_ctx_735_ = lean_ctor_get(v___x_730_, 2);
lean_inc_ref(v_ctx_735_);
lean_dec(v___x_730_);
v_simpTheorems_736_ = lean_ctor_get(v_ctx_734_, 5);
lean_inc_ref(v_simpTheorems_736_);
lean_dec_ref(v_ctx_734_);
v___x_737_ = lean_array_fget_borrowed(v___x_693_, v_a_695_);
v_fvarId_738_ = lean_ctor_get(v___x_737_, 0);
v_userName_739_ = lean_ctor_get(v___x_737_, 1);
v_id_740_ = lean_ctor_get(v___x_737_, 2);
v_origType_741_ = lean_ctor_get(v___x_737_, 3);
v_type_742_ = lean_ctor_get(v___x_737_, 4);
v_proof_743_ = lean_ctor_get(v___x_737_, 5);
v_mvarId_744_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_mvarId_744_);
lean_dec(v___x_732_);
v_usedTheorems_745_ = lean_ctor_get(v___x_733_, 4);
lean_inc_ref(v_usedTheorems_745_);
v_diag_746_ = lean_ctor_get(v___x_733_, 5);
lean_inc_ref(v_diag_746_);
lean_dec(v___x_733_);
lean_inc_ref(v_id_740_);
v___x_747_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(v_simpTheorems_736_, v_id_740_);
v___x_748_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v_ctx_735_, v___x_747_);
v___x_749_ = lean_box(0);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_usedTheorems_745_);
lean_ctor_set(v___x_750_, 1, v_diag_746_);
lean_inc_ref(v___x_694_);
lean_inc_ref(v___x_748_);
lean_inc_ref(v_type_742_);
lean_inc_ref(v_proof_743_);
v___x_751_ = l_Lean_Meta_simpStep(v_mvarId_744_, v_proof_743_, v_type_742_, v___x_748_, v___x_694_, v___x_749_, v___x_728_, v___x_750_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec_ref(v___x_750_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_845_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_845_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_845_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_845_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_fst_756_; lean_object* v_snd_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_844_; 
v_fst_756_ = lean_ctor_get(v_a_752_, 0);
v_snd_757_ = lean_ctor_get(v_a_752_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_a_752_);
if (v_isSharedCheck_844_ == 0)
{
v___x_759_ = v_a_752_;
v_isShared_760_ = v_isSharedCheck_844_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_snd_757_);
lean_inc(v_fst_756_);
lean_dec(v_a_752_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_844_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; uint8_t v_modified_762_; lean_object* v_mvarId_763_; lean_object* v_entries_764_; lean_object* v_ctx_765_; lean_object* v_simprocs_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_841_; 
v___x_761_ = lean_st_ref_take(v___y_697_);
v_modified_762_ = lean_ctor_get_uint8(v___x_761_, sizeof(void*)*6);
v_mvarId_763_ = lean_ctor_get(v___x_761_, 0);
v_entries_764_ = lean_ctor_get(v___x_761_, 1);
v_ctx_765_ = lean_ctor_get(v___x_761_, 2);
v_simprocs_766_ = lean_ctor_get(v___x_761_, 3);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; lean_object* v_unused_843_; 
v_unused_842_ = lean_ctor_get(v___x_761_, 5);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v___x_761_, 4);
lean_dec(v_unused_843_);
v___x_768_ = v___x_761_;
v_isShared_769_ = v_isSharedCheck_841_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_simprocs_766_);
lean_inc(v_ctx_765_);
lean_inc(v_entries_764_);
lean_inc(v_mvarId_763_);
lean_dec(v___x_761_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_841_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_usedTheorems_770_; lean_object* v_diag_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_840_; 
v_usedTheorems_770_ = lean_ctor_get(v_snd_757_, 0);
v_diag_771_ = lean_ctor_get(v_snd_757_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_snd_757_);
if (v_isSharedCheck_840_ == 0)
{
v___x_773_ = v_snd_757_;
v_isShared_774_ = v_isSharedCheck_840_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_diag_771_);
lean_inc(v_usedTheorems_770_);
lean_dec(v_snd_757_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_840_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 5, v_diag_771_);
lean_ctor_set(v___x_768_, 4, v_usedTheorems_770_);
v___x_776_ = v___x_768_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_mvarId_763_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_entries_764_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_ctx_765_);
lean_ctor_set(v_reuseFailAlloc_839_, 3, v_simprocs_766_);
lean_ctor_set(v_reuseFailAlloc_839_, 4, v_usedTheorems_770_);
lean_ctor_set(v_reuseFailAlloc_839_, 5, v_diag_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_839_, sizeof(void*)*6, v_modified_762_);
v___x_776_ = v_reuseFailAlloc_839_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_st_ref_set(v___y_697_, v___x_776_);
v___x_778_ = lean_box(0);
if (lean_obj_tag(v_fst_756_) == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_782_; 
lean_del_object(v___x_773_);
lean_dec_ref(v___x_748_);
lean_dec(v_a_695_);
lean_dec_ref(v___x_694_);
v___x_779_ = lean_box(v___x_728_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v___x_778_);
lean_ctor_set(v___x_759_, 0, v___x_780_);
v___x_782_ = v___x_759_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_778_);
v___x_782_ = v_reuseFailAlloc_786_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_784_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_782_);
v___x_784_ = v___x_754_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_val_787_; lean_object* v_fst_788_; lean_object* v_snd_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_838_; 
lean_del_object(v___x_759_);
lean_del_object(v___x_754_);
v_val_787_ = lean_ctor_get(v_fst_756_, 0);
lean_inc(v_val_787_);
lean_dec_ref(v_fst_756_);
v_fst_788_ = lean_ctor_get(v_val_787_, 0);
v_snd_789_ = lean_ctor_get(v_val_787_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_val_787_);
if (v_isSharedCheck_838_ == 0)
{
v___x_791_ = v_val_787_;
v_isShared_792_ = v_isSharedCheck_838_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_snd_789_);
lean_inc(v_fst_788_);
lean_dec(v_val_787_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_838_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0));
v___x_794_ = lean_expr_eqv(v_snd_789_, v_type_742_);
if (v___x_794_ == 0)
{
lean_object* v_options_795_; lean_object* v_inheritedTraceOptions_796_; uint8_t v_hasTrace_797_; 
v_options_795_ = lean_ctor_get(v___y_700_, 2);
v_inheritedTraceOptions_796_ = lean_ctor_get(v___y_700_, 13);
v_hasTrace_797_ = lean_ctor_get_uint8(v_options_795_, sizeof(void*)*1);
if (v_hasTrace_797_ == 0)
{
lean_del_object(v___x_791_);
lean_del_object(v___x_773_);
goto v___jp_798_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_800_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_801_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8);
v___x_802_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_796_, v_options_795_, v___x_801_);
if (v___x_802_ == 0)
{
lean_del_object(v___x_791_);
lean_del_object(v___x_773_);
goto v___jp_798_;
}
else
{
lean_object* v___x_803_; 
lean_inc_ref(v_id_740_);
v___x_803_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_id_740_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref(v___x_803_);
v___x_805_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10);
if (v_isShared_792_ == 0)
{
lean_ctor_set_tag(v___x_791_, 7);
lean_ctor_set(v___x_791_, 1, v_a_804_);
lean_ctor_set(v___x_791_, 0, v___x_805_);
v___x_807_ = v___x_791_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_a_804_);
v___x_807_ = v_reuseFailAlloc_829_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12);
if (v_isShared_774_ == 0)
{
lean_ctor_set_tag(v___x_773_, 7);
lean_ctor_set(v___x_773_, 1, v___x_808_);
lean_ctor_set(v___x_773_, 0, v___x_807_);
v___x_810_ = v___x_773_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v___x_808_);
v___x_810_ = v_reuseFailAlloc_828_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_inc_ref(v_type_742_);
v___x_811_ = l_Lean_MessageData_ofExpr(v_type_742_);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
lean_inc(v_snd_789_);
v___x_815_ = l_Lean_MessageData_ofExpr(v_snd_789_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v___x_800_, v___x_816_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_819_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref(v___x_817_);
lean_inc_ref(v_origType_741_);
lean_inc(v_userName_739_);
lean_inc(v_fvarId_738_);
v___x_819_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fst_788_, v_snd_789_, v___x_748_, v_fvarId_738_, v___x_728_, v___x_793_, v_a_695_, v___x_778_, v_userName_739_, v_origType_741_, v_a_818_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
v___y_709_ = v___x_819_;
goto v___jp_708_;
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_snd_789_);
lean_dec(v_fst_788_);
lean_dec_ref(v___x_748_);
lean_dec(v_a_695_);
lean_dec_ref(v___x_694_);
v_a_820_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_817_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_817_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_del_object(v___x_791_);
lean_dec(v_snd_789_);
lean_dec(v_fst_788_);
lean_del_object(v___x_773_);
lean_dec_ref(v___x_748_);
lean_dec(v_a_695_);
lean_dec_ref(v___x_694_);
v_a_830_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_803_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_803_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
v___jp_798_:
{
lean_object* v___x_799_; 
lean_inc_ref(v_origType_741_);
lean_inc(v_userName_739_);
lean_inc(v_fvarId_738_);
v___x_799_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fst_788_, v_snd_789_, v___x_748_, v_fvarId_738_, v___x_728_, v___x_793_, v_a_695_, v___x_778_, v_userName_739_, v_origType_741_, v___x_778_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
v___y_709_ = v___x_799_;
goto v___jp_708_;
}
}
else
{
lean_del_object(v___x_791_);
lean_dec(v_snd_789_);
lean_dec(v_fst_788_);
lean_del_object(v___x_773_);
lean_dec_ref(v___x_748_);
v_a_704_ = v___x_793_;
goto v___jp_703_;
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
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec_ref(v___x_748_);
lean_dec(v_a_695_);
lean_dec_ref(v___x_694_);
v_a_846_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_751_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_751_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
v___jp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_nat_add(v_a_695_, v___x_705_);
lean_dec(v_a_695_);
v_a_695_ = v___x_706_;
v_b_696_ = v_a_704_;
goto _start;
}
v___jp_708_:
{
if (lean_obj_tag(v___y_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_719_; 
v_a_710_ = lean_ctor_get(v___y_709_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___y_709_);
if (v_isSharedCheck_719_ == 0)
{
v___x_712_ = v___y_709_;
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___y_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
if (lean_obj_tag(v_a_710_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; 
lean_dec(v_a_695_);
lean_dec_ref(v___x_694_);
v_a_714_ = lean_ctor_get(v_a_710_, 0);
lean_inc(v_a_714_);
lean_dec_ref(v_a_710_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v_a_714_);
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
else
{
lean_object* v_a_718_; 
lean_del_object(v___x_712_);
v_a_718_ = lean_ctor_get(v_a_710_, 0);
lean_inc(v_a_718_);
lean_dec_ref(v_a_710_);
v_a_704_ = v_a_718_;
goto v___jp_703_;
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec(v_a_695_);
lean_dec_ref(v___x_694_);
v_a_720_ = lean_ctor_get(v___y_709_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___y_709_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___y_709_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___y_709_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___boxed(lean_object* v_upperBound_854_, lean_object* v___x_855_, lean_object* v___x_856_, lean_object* v_a_857_, lean_object* v_b_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_upperBound_854_, v___x_855_, v___x_856_, v_a_857_, v_b_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___x_855_);
lean_dec(v_upperBound_854_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___x_886_; lean_object* v_mvarId_887_; lean_object* v_entries_888_; lean_object* v_ctx_889_; lean_object* v_simprocs_890_; lean_object* v_usedTheorems_891_; lean_object* v_diag_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_999_; 
v___x_886_ = lean_st_ref_take(v_a_869_);
v_mvarId_887_ = lean_ctor_get(v___x_886_, 0);
v_entries_888_ = lean_ctor_get(v___x_886_, 1);
v_ctx_889_ = lean_ctor_get(v___x_886_, 2);
v_simprocs_890_ = lean_ctor_get(v___x_886_, 3);
v_usedTheorems_891_ = lean_ctor_get(v___x_886_, 4);
v_diag_892_ = lean_ctor_get(v___x_886_, 5);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_999_ == 0)
{
v___x_894_ = v___x_886_;
v_isShared_895_ = v_isSharedCheck_999_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_diag_892_);
lean_inc(v_usedTheorems_891_);
lean_inc(v_simprocs_890_);
lean_inc(v_ctx_889_);
lean_inc(v_entries_888_);
lean_inc(v_mvarId_887_);
lean_dec(v___x_886_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_999_;
goto v_resetjp_893_;
}
v___jp_875_:
{
lean_object* v___x_881_; uint8_t v_modified_882_; 
v___x_881_ = lean_st_ref_get(v___y_876_);
v_modified_882_ = lean_ctor_get_uint8(v___x_881_, sizeof(void*)*6);
lean_dec(v___x_881_);
if (v_modified_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_box(v_modified_882_);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
return v___x_884_;
}
else
{
v_a_869_ = v___y_876_;
v_a_870_ = v___y_877_;
v_a_871_ = v___y_878_;
v_a_872_ = v___y_879_;
v_a_873_ = v___y_880_;
goto _start;
}
}
v_resetjp_893_:
{
uint8_t v___x_896_; lean_object* v___x_898_; 
v___x_896_ = 0;
if (v_isShared_895_ == 0)
{
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_mvarId_887_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_entries_888_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_ctx_889_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_simprocs_890_);
lean_ctor_set(v_reuseFailAlloc_998_, 4, v_usedTheorems_891_);
lean_ctor_set(v_reuseFailAlloc_998_, 5, v_diag_892_);
v___x_898_ = v_reuseFailAlloc_998_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_entries_902_; lean_object* v_simprocs_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_ctor_set_uint8(v___x_898_, sizeof(void*)*6, v___x_896_);
v___x_899_ = lean_st_ref_set(v_a_869_, v___x_898_);
v___x_900_ = lean_st_ref_get(v_a_869_);
v___x_901_ = lean_st_ref_get(v_a_869_);
v_entries_902_ = lean_ctor_get(v___x_901_, 1);
lean_inc_ref(v_entries_902_);
lean_dec(v___x_901_);
v_simprocs_903_ = lean_ctor_get(v___x_900_, 3);
lean_inc_ref_n(v_simprocs_903_, 2);
lean_dec(v___x_900_);
v___x_904_ = lean_array_get_size(v_entries_902_);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_box(0);
v___x_907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__0));
v___x_908_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v___x_904_, v_entries_902_, v_simprocs_903_, v___x_905_, v___x_907_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec_ref(v_entries_902_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_989_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_989_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_989_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_989_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_fst_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_987_; 
v_fst_913_ = lean_ctor_get(v_a_909_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v_a_909_);
if (v_isSharedCheck_987_ == 0)
{
lean_object* v_unused_988_; 
v_unused_988_ = lean_ctor_get(v_a_909_, 1);
lean_dec(v_unused_988_);
v___x_915_ = v_a_909_;
v_isShared_916_ = v_isSharedCheck_987_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_fst_913_);
lean_dec(v_a_909_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_987_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
if (lean_obj_tag(v_fst_913_) == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v_mvarId_920_; lean_object* v_ctx_921_; lean_object* v_usedTheorems_922_; lean_object* v_diag_923_; uint8_t v___x_924_; lean_object* v___x_926_; 
lean_del_object(v___x_911_);
v___x_917_ = lean_st_ref_get(v_a_869_);
v___x_918_ = lean_st_ref_get(v_a_869_);
v___x_919_ = lean_st_ref_get(v_a_869_);
v_mvarId_920_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_mvarId_920_);
lean_dec(v___x_917_);
v_ctx_921_ = lean_ctor_get(v___x_918_, 2);
lean_inc_ref(v_ctx_921_);
lean_dec(v___x_918_);
v_usedTheorems_922_ = lean_ctor_get(v___x_919_, 4);
lean_inc_ref(v_usedTheorems_922_);
v_diag_923_ = lean_ctor_get(v___x_919_, 5);
lean_inc_ref(v_diag_923_);
lean_dec(v___x_919_);
v___x_924_ = 1;
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 1, v_diag_923_);
lean_ctor_set(v___x_915_, 0, v_usedTheorems_922_);
v___x_926_ = v___x_915_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_usedTheorems_922_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_diag_923_);
v___x_926_ = v_reuseFailAlloc_982_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; 
lean_inc(v_mvarId_920_);
v___x_927_ = l_Lean_Meta_simpTarget(v_mvarId_920_, v_ctx_921_, v_simprocs_903_, v___x_906_, v___x_924_, v___x_926_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_973_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_973_ == 0)
{
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_973_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_973_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_fst_932_; lean_object* v_snd_933_; lean_object* v___x_934_; uint8_t v_modified_935_; lean_object* v_mvarId_936_; lean_object* v_entries_937_; lean_object* v_ctx_938_; lean_object* v_simprocs_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_970_; 
v_fst_932_ = lean_ctor_get(v_a_928_, 0);
lean_inc(v_fst_932_);
v_snd_933_ = lean_ctor_get(v_a_928_, 1);
lean_inc(v_snd_933_);
lean_dec(v_a_928_);
v___x_934_ = lean_st_ref_take(v_a_869_);
v_modified_935_ = lean_ctor_get_uint8(v___x_934_, sizeof(void*)*6);
v_mvarId_936_ = lean_ctor_get(v___x_934_, 0);
v_entries_937_ = lean_ctor_get(v___x_934_, 1);
v_ctx_938_ = lean_ctor_get(v___x_934_, 2);
v_simprocs_939_ = lean_ctor_get(v___x_934_, 3);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; lean_object* v_unused_972_; 
v_unused_971_ = lean_ctor_get(v___x_934_, 5);
lean_dec(v_unused_971_);
v_unused_972_ = lean_ctor_get(v___x_934_, 4);
lean_dec(v_unused_972_);
v___x_941_ = v___x_934_;
v_isShared_942_ = v_isSharedCheck_970_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_simprocs_939_);
lean_inc(v_ctx_938_);
lean_inc(v_entries_937_);
lean_inc(v_mvarId_936_);
lean_dec(v___x_934_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_970_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_usedTheorems_943_; lean_object* v_diag_944_; lean_object* v___x_946_; 
v_usedTheorems_943_ = lean_ctor_get(v_snd_933_, 0);
lean_inc_ref(v_usedTheorems_943_);
v_diag_944_ = lean_ctor_get(v_snd_933_, 1);
lean_inc_ref(v_diag_944_);
lean_dec(v_snd_933_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 5, v_diag_944_);
lean_ctor_set(v___x_941_, 4, v_usedTheorems_943_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_mvarId_936_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_entries_937_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_ctx_938_);
lean_ctor_set(v_reuseFailAlloc_969_, 3, v_simprocs_939_);
lean_ctor_set(v_reuseFailAlloc_969_, 4, v_usedTheorems_943_);
lean_ctor_set(v_reuseFailAlloc_969_, 5, v_diag_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_969_, sizeof(void*)*6, v_modified_935_);
v___x_946_ = v_reuseFailAlloc_969_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; 
v___x_947_ = lean_st_ref_set(v_a_869_, v___x_946_);
if (lean_obj_tag(v_fst_932_) == 0)
{
lean_object* v___x_948_; lean_object* v___x_950_; 
lean_dec(v_mvarId_920_);
v___x_948_ = lean_box(v___x_924_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_948_);
v___x_950_ = v___x_930_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
else
{
lean_object* v_val_952_; uint8_t v___x_953_; 
lean_del_object(v___x_930_);
v_val_952_ = lean_ctor_get(v_fst_932_, 0);
lean_inc(v_val_952_);
lean_dec_ref(v_fst_932_);
v___x_953_ = l_Lean_instBEqMVarId_beq(v_mvarId_920_, v_val_952_);
lean_dec(v_mvarId_920_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; lean_object* v_entries_955_; lean_object* v_ctx_956_; lean_object* v_simprocs_957_; lean_object* v_usedTheorems_958_; lean_object* v_diag_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_967_; 
v___x_954_ = lean_st_ref_take(v_a_869_);
v_entries_955_ = lean_ctor_get(v___x_954_, 1);
v_ctx_956_ = lean_ctor_get(v___x_954_, 2);
v_simprocs_957_ = lean_ctor_get(v___x_954_, 3);
v_usedTheorems_958_ = lean_ctor_get(v___x_954_, 4);
v_diag_959_ = lean_ctor_get(v___x_954_, 5);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; 
v_unused_968_ = lean_ctor_get(v___x_954_, 0);
lean_dec(v_unused_968_);
v___x_961_ = v___x_954_;
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_diag_959_);
lean_inc(v_usedTheorems_958_);
lean_inc(v_simprocs_957_);
lean_inc(v_ctx_956_);
lean_inc(v_entries_955_);
lean_dec(v___x_954_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v_val_952_);
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_val_952_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_entries_955_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_ctx_956_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_simprocs_957_);
lean_ctor_set(v_reuseFailAlloc_966_, 4, v_usedTheorems_958_);
lean_ctor_set(v_reuseFailAlloc_966_, 5, v_diag_959_);
v___x_964_ = v_reuseFailAlloc_966_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; 
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*6, v___x_924_);
v___x_965_ = lean_st_ref_set(v_a_869_, v___x_964_);
v___y_876_ = v_a_869_;
v___y_877_ = v_a_870_;
v___y_878_ = v_a_871_;
v___y_879_ = v_a_872_;
v___y_880_ = v_a_873_;
goto v___jp_875_;
}
}
}
else
{
lean_dec(v_val_952_);
v___y_876_ = v_a_869_;
v___y_877_ = v_a_870_;
v___y_878_ = v_a_871_;
v___y_879_ = v_a_872_;
v___y_880_ = v_a_873_;
goto v___jp_875_;
}
}
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v_mvarId_920_);
v_a_974_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_927_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_927_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
else
{
lean_object* v_val_983_; lean_object* v___x_985_; 
lean_del_object(v___x_915_);
lean_dec_ref(v_simprocs_903_);
v_val_983_ = lean_ctor_get(v_fst_913_, 0);
lean_inc(v_val_983_);
lean_dec_ref(v_fst_913_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_val_983_);
v___x_985_ = v___x_911_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_val_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec_ref(v_simprocs_903_);
v_a_990_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_908_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_908_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___boxed(lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(lean_object* v_cls_1007_, lean_object* v_msg_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_cls_1007_, v_msg_1008_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___boxed(lean_object* v_cls_1016_, lean_object* v_msg_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(v_cls_1016_, v_msg_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(lean_object* v_upperBound_1025_, lean_object* v___x_1026_, lean_object* v___x_1027_, lean_object* v_inst_1028_, lean_object* v_R_1029_, lean_object* v_a_1030_, lean_object* v_b_1031_, lean_object* v_c_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_upperBound_1025_, v___x_1026_, v___x_1027_, v_a_1030_, v_b_1031_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___boxed(lean_object* v_upperBound_1040_, lean_object* v___x_1041_, lean_object* v___x_1042_, lean_object* v_inst_1043_, lean_object* v_R_1044_, lean_object* v_a_1045_, lean_object* v_b_1046_, lean_object* v_c_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(v_upperBound_1040_, v___x_1041_, v___x_1042_, v_inst_1043_, v_R_1044_, v_a_1045_, v_b_1046_, v_c_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___x_1041_);
lean_dec(v_upperBound_1040_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(lean_object* v_as_1055_, size_t v_sz_1056_, size_t v_i_1057_, lean_object* v_b_1058_){
_start:
{
lean_object* v_a_1061_; uint8_t v___x_1065_; 
v___x_1065_ = lean_usize_dec_lt(v_i_1057_, v_sz_1056_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_b_1058_);
return v___x_1066_;
}
else
{
lean_object* v_snd_1067_; lean_object* v_fst_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1105_; 
v_snd_1067_ = lean_ctor_get(v_b_1058_, 1);
v_fst_1068_ = lean_ctor_get(v_b_1058_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_b_1058_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1070_ = v_b_1058_;
v_isShared_1071_ = v_isSharedCheck_1105_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_snd_1067_);
lean_inc(v_fst_1068_);
lean_dec(v_b_1058_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1105_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v_fst_1072_; lean_object* v_snd_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1104_; 
v_fst_1072_ = lean_ctor_get(v_snd_1067_, 0);
v_snd_1073_ = lean_ctor_get(v_snd_1067_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_snd_1067_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1075_ = v_snd_1067_;
v_isShared_1076_ = v_isSharedCheck_1104_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_snd_1073_);
lean_inc(v_fst_1072_);
lean_dec(v_snd_1067_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1104_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_a_1077_; lean_object* v_fvarId_1078_; lean_object* v_userName_1079_; lean_object* v_origType_1080_; lean_object* v_type_1081_; lean_object* v_proof_1082_; uint8_t v___x_1096_; 
v_a_1077_ = lean_array_uget_borrowed(v_as_1055_, v_i_1057_);
v_fvarId_1078_ = lean_ctor_get(v_a_1077_, 0);
v_userName_1079_ = lean_ctor_get(v_a_1077_, 1);
v_origType_1080_ = lean_ctor_get(v_a_1077_, 3);
v_type_1081_ = lean_ctor_get(v_a_1077_, 4);
v_proof_1082_ = lean_ctor_get(v_a_1077_, 5);
lean_inc_ref(v_type_1081_);
v___x_1096_ = l_Lean_Expr_isTrue(v_type_1081_);
if (v___x_1096_ == 0)
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_unbox(v_snd_1073_);
if (v___x_1097_ == 0)
{
uint8_t v___x_1098_; 
v___x_1098_ = lean_expr_eqv(v_type_1081_, v_origType_1080_);
if (v___x_1098_ == 0)
{
lean_dec(v_snd_1073_);
goto v___jp_1083_;
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_del_object(v___x_1075_);
lean_del_object(v___x_1070_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_fst_1072_);
lean_ctor_set(v___x_1099_, 1, v_snd_1073_);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v_fst_1068_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v_a_1061_ = v___x_1100_;
goto v___jp_1060_;
}
}
else
{
lean_dec(v_snd_1073_);
goto v___jp_1083_;
}
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_del_object(v___x_1075_);
lean_del_object(v___x_1070_);
lean_inc(v_fvarId_1078_);
v___x_1101_ = lean_array_push(v_fst_1072_, v_fvarId_1078_);
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v_snd_1073_);
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v_fst_1068_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v_a_1061_ = v___x_1103_;
goto v___jp_1060_;
}
v___jp_1083_:
{
lean_object* v___x_1084_; uint8_t v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
lean_inc(v_fvarId_1078_);
v___x_1084_ = lean_array_push(v_fst_1072_, v_fvarId_1078_);
v___x_1085_ = 0;
v___x_1086_ = 0;
lean_inc_ref(v_proof_1082_);
lean_inc_ref(v_type_1081_);
lean_inc(v_userName_1079_);
v___x_1087_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1087_, 0, v_userName_1079_);
lean_ctor_set(v___x_1087_, 1, v_type_1081_);
lean_ctor_set(v___x_1087_, 2, v_proof_1082_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*3, v___x_1085_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*3 + 1, v___x_1086_);
v___x_1088_ = lean_array_push(v_fst_1068_, v___x_1087_);
v___x_1089_ = lean_box(v___x_1065_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v___x_1089_);
lean_ctor_set(v___x_1075_, 0, v___x_1084_);
v___x_1091_ = v___x_1075_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v___x_1091_);
lean_ctor_set(v___x_1070_, 0, v___x_1088_);
v___x_1093_ = v___x_1070_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
v_a_1061_ = v___x_1093_;
goto v___jp_1060_;
}
}
}
}
}
}
v___jp_1060_:
{
size_t v___x_1062_; size_t v___x_1063_; 
v___x_1062_ = ((size_t)1ULL);
v___x_1063_ = lean_usize_add(v_i_1057_, v___x_1062_);
v_i_1057_ = v___x_1063_;
v_b_1058_ = v_a_1061_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg___boxed(lean_object* v_as_1106_, lean_object* v_sz_1107_, lean_object* v_i_1108_, lean_object* v_b_1109_, lean_object* v___y_1110_){
_start:
{
size_t v_sz_boxed_1111_; size_t v_i_boxed_1112_; lean_object* v_res_1113_; 
v_sz_boxed_1111_ = lean_unbox_usize(v_sz_1107_);
lean_dec(v_sz_1107_);
v_i_boxed_1112_ = lean_unbox_usize(v_i_1108_);
lean_dec(v_i_1108_);
v_res_1113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_as_1106_, v_sz_boxed_1111_, v_i_boxed_1112_, v_b_1109_);
lean_dec_ref(v_as_1106_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_main(lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v___x_1123_; 
lean_dec_ref(v___x_1122_);
v___x_1123_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1184_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1184_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1184_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_unbox(v_a_1124_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v_entries_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; size_t v_sz_1135_; size_t v___x_1136_; lean_object* v___x_1137_; 
lean_del_object(v___x_1126_);
v___x_1129_ = lean_st_ref_get(v_a_1116_);
v___x_1130_ = lean_st_ref_get(v_a_1116_);
v_entries_1131_ = lean_ctor_get(v___x_1130_, 1);
lean_inc_ref(v_entries_1131_);
lean_dec(v___x_1130_);
v___x_1132_ = ((lean_object*)(l_Lean_Meta_SimpAll_main___closed__0));
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_ctor_set(v___x_1133_, 1, v_a_1124_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v_sz_1135_ = lean_array_size(v_entries_1131_);
v___x_1136_ = ((size_t)0ULL);
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_entries_1131_, v_sz_1135_, v___x_1136_, v___x_1134_);
lean_dec_ref(v_entries_1131_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v_mvarId_1139_; lean_object* v_fst_1140_; lean_object* v_snd_1141_; lean_object* v___x_1142_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref(v___x_1137_);
v_mvarId_1139_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_mvarId_1139_);
lean_dec(v___x_1129_);
v_fst_1140_ = lean_ctor_get(v_a_1138_, 0);
lean_inc(v_fst_1140_);
v_snd_1141_ = lean_ctor_get(v_a_1138_, 1);
lean_inc(v_snd_1141_);
lean_dec(v_a_1138_);
v___x_1142_ = l_Lean_MVarId_assertHypotheses(v_mvarId_1139_, v_fst_1140_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v_snd_1144_; lean_object* v_fst_1145_; lean_object* v___x_1146_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref(v___x_1142_);
v_snd_1144_ = lean_ctor_get(v_a_1143_, 1);
lean_inc(v_snd_1144_);
lean_dec(v_a_1143_);
v_fst_1145_ = lean_ctor_get(v_snd_1141_, 0);
lean_inc(v_fst_1145_);
lean_dec(v_snd_1141_);
v___x_1146_ = l_Lean_MVarId_tryClearMany(v_snd_1144_, v_fst_1145_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_fst_1145_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1155_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_a_1147_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1151_);
v___x_1153_ = v___x_1149_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
v_a_1156_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1146_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1146_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_snd_1141_);
v_a_1164_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1142_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1142_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v___x_1129_);
v_a_1172_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1137_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1137_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
lean_dec(v_a_1124_);
v___x_1180_ = lean_box(0);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1180_);
v___x_1182_ = v___x_1126_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
v_a_1185_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1123_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1123_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
v_a_1193_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1122_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1122_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_main___boxed(lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Meta_SimpAll_main(v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(lean_object* v_as_1208_, size_t v_sz_1209_, size_t v_i_1210_, lean_object* v_b_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_as_1208_, v_sz_1209_, v_i_1210_, v_b_1211_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___boxed(lean_object* v_as_1219_, lean_object* v_sz_1220_, lean_object* v_i_1221_, lean_object* v_b_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
size_t v_sz_boxed_1229_; size_t v_i_boxed_1230_; lean_object* v_res_1231_; 
v_sz_boxed_1229_ = lean_unbox_usize(v_sz_1220_);
lean_dec(v_sz_1220_);
v_i_boxed_1230_ = lean_unbox_usize(v_i_1221_);
lean_dec(v_i_1221_);
v_res_1231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(v_as_1219_, v_sz_boxed_1229_, v_i_boxed_1230_, v_b_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v_as_1219_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(lean_object* v_mvarId_1232_, lean_object* v_x_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1232_, v_x_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
v_a_1248_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1239_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1239_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg___boxed(lean_object* v_mvarId_1256_, lean_object* v_x_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1256_, v_x_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(lean_object* v_00_u03b1_1264_, lean_object* v_mvarId_1265_, lean_object* v_x_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1265_, v_x_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___boxed(lean_object* v_00_u03b1_1273_, lean_object* v_mvarId_1274_, lean_object* v_x_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(v_00_u03b1_1273_, v_mvarId_1274_, v_x_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(lean_object* v_msg_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_ref_1288_; lean_object* v___x_1289_; lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1298_; 
v_ref_1288_ = lean_ctor_get(v___y_1285_, 5);
v___x_1289_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msg_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1298_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1298_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
lean_inc(v_ref_1288_);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_ref_1288_);
lean_ctor_set(v___x_1294_, 1, v_a_1290_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set_tag(v___x_1292_, 1);
lean_ctor_set(v___x_1292_, 0, v___x_1294_);
v___x_1296_ = v___x_1292_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg___boxed(lean_object* v_msg_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v_msg_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
return v_res_1305_;
}
}
static lean_object* _init_l_Lean_Meta_simpAll___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_Lean_Meta_simpAll___lam__0___closed__0));
v___x_1308_ = l_Lean_stringToMessageData(v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___lam__0(lean_object* v___x_1309_, lean_object* v_ctx_1310_, lean_object* v_mvarId_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_st_mk_ref(v___x_1309_);
v___x_1318_ = l_Lean_Meta_SimpAll_main(v___x_1317_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1346_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1346_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1346_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_st_ref_get(v___x_1317_);
lean_dec(v___x_1317_);
if (lean_obj_tag(v_a_1319_) == 1)
{
lean_object* v_config_1332_; uint8_t v_failIfUnchanged_1333_; 
v_config_1332_ = lean_ctor_get(v_ctx_1310_, 0);
v_failIfUnchanged_1333_ = lean_ctor_get_uint8(v_config_1332_, sizeof(void*)*3 + 13);
if (v_failIfUnchanged_1333_ == 0)
{
goto v___jp_1324_;
}
else
{
lean_object* v_val_1334_; uint8_t v___x_1335_; 
v_val_1334_ = lean_ctor_get(v_a_1319_, 0);
v___x_1335_ = l_Lean_instBEqMVarId_beq(v_mvarId_1311_, v_val_1334_);
if (v___x_1335_ == 0)
{
goto v___jp_1324_;
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec_ref(v_a_1319_);
lean_dec(v___x_1323_);
lean_del_object(v___x_1321_);
v___x_1336_ = lean_obj_once(&l_Lean_Meta_simpAll___lam__0___closed__1, &l_Lean_Meta_simpAll___lam__0___closed__1_once, _init_l_Lean_Meta_simpAll___lam__0___closed__1);
v___x_1337_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v___x_1336_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
else
{
goto v___jp_1324_;
}
v___jp_1324_:
{
lean_object* v_usedTheorems_1325_; lean_object* v_diag_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v_usedTheorems_1325_ = lean_ctor_get(v___x_1323_, 4);
lean_inc_ref(v_usedTheorems_1325_);
v_diag_1326_ = lean_ctor_get(v___x_1323_, 5);
lean_inc_ref(v_diag_1326_);
lean_dec(v___x_1323_);
v___x_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1327_, 0, v_usedTheorems_1325_);
lean_ctor_set(v___x_1327_, 1, v_diag_1326_);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v_a_1319_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1328_);
v___x_1330_ = v___x_1321_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec(v___x_1317_);
v_a_1347_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1318_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1318_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___lam__0___boxed(lean_object* v___x_1355_, lean_object* v_ctx_1356_, lean_object* v_mvarId_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Meta_simpAll___lam__0(v___x_1355_, v_ctx_1356_, v_mvarId_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v_mvarId_1357_);
lean_dec_ref(v_ctx_1356_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll(lean_object* v_mvarId_1366_, lean_object* v_ctx_1367_, lean_object* v_simprocs_1368_, lean_object* v_stats_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_usedTheorems_1375_; lean_object* v_diag_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___f_1380_; lean_object* v___x_1381_; 
v_usedTheorems_1375_ = lean_ctor_get(v_stats_1369_, 0);
v_diag_1376_ = lean_ctor_get(v_stats_1369_, 1);
v___x_1377_ = 0;
v___x_1378_ = ((lean_object*)(l_Lean_Meta_simpAll___closed__0));
lean_inc_ref(v_diag_1376_);
lean_inc_ref(v_usedTheorems_1375_);
lean_inc_ref(v_ctx_1367_);
lean_inc_n(v_mvarId_1366_, 2);
v___x_1379_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1379_, 0, v_mvarId_1366_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
lean_ctor_set(v___x_1379_, 2, v_ctx_1367_);
lean_ctor_set(v___x_1379_, 3, v_simprocs_1368_);
lean_ctor_set(v___x_1379_, 4, v_usedTheorems_1375_);
lean_ctor_set(v___x_1379_, 5, v_diag_1376_);
lean_ctor_set_uint8(v___x_1379_, sizeof(void*)*6, v___x_1377_);
v___f_1380_ = lean_alloc_closure((void*)(l_Lean_Meta_simpAll___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1380_, 0, v___x_1379_);
lean_closure_set(v___f_1380_, 1, v_ctx_1367_);
lean_closure_set(v___f_1380_, 2, v_mvarId_1366_);
v___x_1381_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1366_, v___f_1380_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___boxed(lean_object* v_mvarId_1382_, lean_object* v_ctx_1383_, lean_object* v_simprocs_1384_, lean_object* v_stats_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_Meta_simpAll(v_mvarId_1382_, v_ctx_1383_, v_simprocs_1384_, v_stats_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec_ref(v_stats_1385_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(lean_object* v_00_u03b1_1392_, lean_object* v_msg_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v_msg_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___boxed(lean_object* v_00_u03b1_1400_, lean_object* v_msg_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(v_00_u03b1_1400_, v_msg_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1477_; uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1477_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_1478_ = 0;
v___x_1479_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_));
v___x_1480_ = l_Lean_registerTraceClass(v___x_1477_, v___x_1478_, v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2____boxed(lean_object* v_a_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_();
return v_res_1482_;
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
