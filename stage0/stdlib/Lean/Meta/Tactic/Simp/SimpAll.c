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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0(lean_object* v_x_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
lean_inc(v___y_14_);
v___x_20_ = lean_apply_6(v_x_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, lean_box(0));
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_13_ = stack[0].m_obj;
lean_object* v___y_14_ = stack[1].m_obj;
lean_object* v___y_15_ = stack[2].m_obj;
lean_object* v___y_16_ = stack[3].m_obj;
lean_object* v___y_17_ = stack[4].m_obj;
lean_object* v___y_18_ = stack[5].m_obj;
lean_object* v_res_21_;
v_res_21_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___lam__0(v_x_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_21_;
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
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(lean_object* v_mvarId_30_, lean_object* v_x_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_30_ = stack[0].m_obj;
lean_object* v_x_31_ = stack[1].m_obj;
lean_object* v___y_32_ = stack[2].m_obj;
lean_object* v___y_33_ = stack[3].m_obj;
lean_object* v___y_34_ = stack[4].m_obj;
lean_object* v___y_35_ = stack[5].m_obj;
lean_object* v___y_36_ = stack[6].m_obj;
lean_object* v_res_48_;
v_res_48_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_30_, v_x_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg___boxed(lean_object* v_mvarId_49_, lean_object* v_x_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_49_, v_x_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
return v_res_57_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0(lean_object* v_00_u03b1_58_, lean_object* v_mvarId_59_, lean_object* v_x_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_59_, v_x_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
return v___x_67_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_59_ = stack[1].m_obj;
lean_object* v_x_60_ = stack[2].m_obj;
lean_object* v___y_61_ = stack[3].m_obj;
lean_object* v___y_62_ = stack[4].m_obj;
lean_object* v___y_63_ = stack[5].m_obj;
lean_object* v___y_64_ = stack[6].m_obj;
lean_object* v___y_65_ = stack[7].m_obj;
lean_object* v_res_68_;
v_res_68_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0(lean_box(0), v_mvarId_59_, v_x_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___boxed(lean_object* v_00_u03b1_69_, lean_object* v_mvarId_70_, lean_object* v_x_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0(v_00_u03b1_69_, v_mvarId_70_, v_x_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
return v_res_78_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(lean_object* v_e_79_, lean_object* v___y_80_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = l_Lean_Expr_hasMVar(v_e_79_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v_e_79_);
return v___x_83_;
}
else
{
lean_object* v___x_84_; lean_object* v_mctx_85_; lean_object* v___x_86_; lean_object* v_fst_87_; lean_object* v_snd_88_; lean_object* v___x_89_; lean_object* v_cache_90_; lean_object* v_zetaDeltaFVarIds_91_; lean_object* v_postponed_92_; lean_object* v_diag_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_102_; 
v___x_84_ = lean_st_ref_get(v___y_80_);
v_mctx_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc_ref(v_mctx_85_);
lean_dec(v___x_84_);
v___x_86_ = l_Lean_instantiateMVarsCore(v_mctx_85_, v_e_79_);
v_fst_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_fst_87_);
v_snd_88_ = lean_ctor_get(v___x_86_, 1);
lean_inc(v_snd_88_);
lean_dec_ref(v___x_86_);
v___x_89_ = lean_st_ref_take(v___y_80_);
v_cache_90_ = lean_ctor_get(v___x_89_, 1);
v_zetaDeltaFVarIds_91_ = lean_ctor_get(v___x_89_, 2);
v_postponed_92_ = lean_ctor_get(v___x_89_, 3);
v_diag_93_ = lean_ctor_get(v___x_89_, 4);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v___x_89_, 0);
lean_dec(v_unused_103_);
v___x_95_ = v___x_89_;
v_isShared_96_ = v_isSharedCheck_102_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_diag_93_);
lean_inc(v_postponed_92_);
lean_inc(v_zetaDeltaFVarIds_91_);
lean_inc(v_cache_90_);
lean_dec(v___x_89_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_102_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v_snd_88_);
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_snd_88_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_cache_90_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_zetaDeltaFVarIds_91_);
lean_ctor_set(v_reuseFailAlloc_101_, 3, v_postponed_92_);
lean_ctor_set(v_reuseFailAlloc_101_, 4, v_diag_93_);
v___x_98_ = v_reuseFailAlloc_101_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_st_ref_put(v___y_80_, v___x_98_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v_fst_87_);
return v___x_100_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_79_ = stack[0].m_obj;
lean_object* v___y_80_ = stack[1].m_obj;
lean_object* v_res_104_;
v_res_104_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(v_e_79_, v___y_80_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg___boxed(lean_object* v_e_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(v_e_105_, v___y_106_);
lean_dec(v___y_106_);
return v_res_108_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2(lean_object* v_e_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(v_e_109_, v___y_112_);
return v___x_116_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_109_ = stack[0].m_obj;
lean_object* v___y_110_ = stack[1].m_obj;
lean_object* v___y_111_ = stack[2].m_obj;
lean_object* v___y_112_ = stack[3].m_obj;
lean_object* v___y_113_ = stack[4].m_obj;
lean_object* v___y_114_ = stack[5].m_obj;
lean_object* v_res_117_;
v_res_117_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2(v_e_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
stack->m_obj
 = v_res_117_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___boxed(lean_object* v_e_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2(v_e_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
return v_res_125_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0(lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Meta_getPropHyps(v___y_127_, v___y_128_, v___y_129_, v___y_130_);
return v___x_132_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_126_ = stack[0].m_obj;
lean_object* v___y_127_ = stack[1].m_obj;
lean_object* v___y_128_ = stack[2].m_obj;
lean_object* v___y_129_ = stack[3].m_obj;
lean_object* v___y_130_ = stack[4].m_obj;
lean_object* v_res_133_;
v_res_133_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0(v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0___boxed(lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___lam__0(v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
return v_res_140_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(lean_object* v_a_141_, lean_object* v_as_142_, size_t v_i_143_, size_t v_stop_144_){
_start:
{
uint8_t v___x_145_; 
v___x_145_ = lean_usize_dec_eq(v_i_143_, v_stop_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = lean_array_uget_borrowed(v_as_142_, v_i_143_);
v___x_147_ = l_Lean_instBEqFVarId_beq(v_a_141_, v___x_146_);
if (v___x_147_ == 0)
{
size_t v___x_148_; size_t v___x_149_; 
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_add(v_i_143_, v___x_148_);
v_i_143_ = v___x_149_;
goto _start;
}
else
{
return v___x_147_;
}
}
else
{
uint8_t v___x_151_; 
v___x_151_ = 0;
return v___x_151_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_141_ = stack[0].m_obj;
lean_object* v_as_142_ = stack[1].m_obj;
size_t v_i_143_ = stack[2].m_num;
size_t v_stop_144_ = stack[3].m_num;
uint8_t v_res_152_;
v_res_152_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(v_a_141_, v_as_142_, v_i_143_, v_stop_144_);
stack->m_num = v_res_152_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1___boxed(lean_object* v_a_153_, lean_object* v_as_154_, lean_object* v_i_155_, lean_object* v_stop_156_){
_start:
{
size_t v_i_boxed_157_; size_t v_stop_boxed_158_; uint8_t v_res_159_; lean_object* v_r_160_; 
v_i_boxed_157_ = lean_unbox_usize(v_i_155_);
lean_dec(v_i_155_);
v_stop_boxed_158_ = lean_unbox_usize(v_stop_156_);
lean_dec(v_stop_156_);
v_res_159_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(v_a_153_, v_as_154_, v_i_boxed_157_, v_stop_boxed_158_);
lean_dec_ref(v_as_154_);
lean_dec(v_a_153_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(lean_object* v_as_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_array_get_size(v_as_161_);
v___x_165_ = lean_nat_dec_lt(v___x_163_, v___x_164_);
if (v___x_165_ == 0)
{
return v___x_165_;
}
else
{
if (v___x_165_ == 0)
{
return v___x_165_;
}
else
{
size_t v___x_166_; size_t v___x_167_; uint8_t v___x_168_; 
v___x_166_ = ((size_t)0ULL);
v___x_167_ = lean_usize_of_nat(v___x_164_);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_spec__1(v_a_162_, v_as_161_, v___x_166_, v___x_167_);
return v___x_168_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_161_ = stack[0].m_obj;
lean_object* v_a_162_ = stack[1].m_obj;
uint8_t v_res_169_;
v_res_169_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(v_as_161_, v_a_162_);
stack->m_num = v_res_169_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1___boxed(lean_object* v_as_170_, lean_object* v_a_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(v_as_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_as_170_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(lean_object* v_a_174_, lean_object* v_as_175_, size_t v_sz_176_, size_t v_i_177_, lean_object* v_b_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_a_186_; uint8_t v___x_190_; 
v___x_190_ = lean_usize_dec_lt(v_i_177_, v_sz_176_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v_b_178_);
return v___x_191_;
}
else
{
lean_object* v_a_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_a_192_ = lean_array_uget_borrowed(v_as_175_, v_i_177_);
lean_inc(v_a_192_);
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v_a_192_);
v___x_194_ = l_Lean_Meta_SimpTheoremsArray_isErased(v_b_178_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_inc(v_a_192_);
v___x_195_ = l_Lean_FVarId_getDecl___redArg(v_a_192_, v___y_180_, v___y_182_, v___y_183_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_ctx_199_; lean_object* v_indexConfig_200_; lean_object* v___x_201_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc_n(v_a_196_, 2);
lean_dec_ref_known(v___x_195_, 1);
v___x_197_ = l_Lean_LocalDecl_toExpr(v_a_196_);
v___x_198_ = lean_st_ref_get(v___y_179_);
v_ctx_199_ = lean_ctor_get(v___x_198_, 2);
lean_inc_ref(v_ctx_199_);
lean_dec(v___x_198_);
v_indexConfig_200_ = lean_ctor_get(v_ctx_199_, 5);
lean_inc_ref(v_indexConfig_200_);
lean_dec_ref(v_ctx_199_);
lean_inc_ref(v___x_197_);
lean_inc_ref(v___x_193_);
v___x_201_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v_b_178_, v___x_193_, v___x_197_, v_indexConfig_200_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_203_; uint8_t v_modified_204_; lean_object* v_mvarId_205_; lean_object* v_entries_206_; lean_object* v_ctx_207_; lean_object* v_simprocs_208_; lean_object* v_usedTheorems_209_; lean_object* v_diag_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_250_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_201_, 1);
v___x_203_ = lean_st_ref_take(v___y_179_);
v_modified_204_ = lean_ctor_get_uint8(v___x_203_, sizeof(void*)*6);
v_mvarId_205_ = lean_ctor_get(v___x_203_, 0);
v_entries_206_ = lean_ctor_get(v___x_203_, 1);
v_ctx_207_ = lean_ctor_get(v___x_203_, 2);
v_simprocs_208_ = lean_ctor_get(v___x_203_, 3);
v_usedTheorems_209_ = lean_ctor_get(v___x_203_, 4);
v_diag_210_ = lean_ctor_get(v___x_203_, 5);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_250_ == 0)
{
v___x_212_ = v___x_203_;
v_isShared_213_ = v_isSharedCheck_250_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_diag_210_);
lean_inc(v_usedTheorems_209_);
lean_inc(v_simprocs_208_);
lean_inc(v_ctx_207_);
lean_inc(v_entries_206_);
lean_inc(v_mvarId_205_);
lean_dec(v___x_203_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_250_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
lean_inc(v_a_202_);
v___x_214_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v_ctx_207_, v_a_202_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 2, v___x_214_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_mvarId_205_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_entries_206_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_249_, 3, v_simprocs_208_);
lean_ctor_set(v_reuseFailAlloc_249_, 4, v_usedTheorems_209_);
lean_ctor_set(v_reuseFailAlloc_249_, 5, v_diag_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_249_, sizeof(void*)*6, v_modified_204_);
v___x_216_ = v_reuseFailAlloc_249_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_st_ref_put(v___y_179_, v___x_216_);
v___x_218_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__1(v_a_174_, v_a_192_);
if (v___x_218_ == 0)
{
lean_dec_ref(v___x_197_);
lean_dec(v_a_196_);
lean_dec_ref_known(v___x_193_, 1);
v_a_186_ = v_a_202_;
goto v___jp_185_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = l_Lean_LocalDecl_type(v_a_196_);
v___x_220_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__2___redArg(v___x_219_, v___y_181_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v_modified_225_; lean_object* v_mvarId_226_; lean_object* v_entries_227_; lean_object* v_ctx_228_; lean_object* v_simprocs_229_; lean_object* v_usedTheorems_230_; lean_object* v_diag_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_240_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc_n(v_a_221_, 2);
lean_dec_ref_known(v___x_220_, 1);
v___x_222_ = l_Lean_LocalDecl_userName(v_a_196_);
lean_dec(v_a_196_);
lean_inc(v_a_192_);
v___x_223_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_223_, 0, v_a_192_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
lean_ctor_set(v___x_223_, 2, v___x_193_);
lean_ctor_set(v___x_223_, 3, v_a_221_);
lean_ctor_set(v___x_223_, 4, v_a_221_);
lean_ctor_set(v___x_223_, 5, v___x_197_);
v___x_224_ = lean_st_ref_take(v___y_179_);
v_modified_225_ = lean_ctor_get_uint8(v___x_224_, sizeof(void*)*6);
v_mvarId_226_ = lean_ctor_get(v___x_224_, 0);
v_entries_227_ = lean_ctor_get(v___x_224_, 1);
v_ctx_228_ = lean_ctor_get(v___x_224_, 2);
v_simprocs_229_ = lean_ctor_get(v___x_224_, 3);
v_usedTheorems_230_ = lean_ctor_get(v___x_224_, 4);
v_diag_231_ = lean_ctor_get(v___x_224_, 5);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_240_ == 0)
{
v___x_233_ = v___x_224_;
v_isShared_234_ = v_isSharedCheck_240_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_diag_231_);
lean_inc(v_usedTheorems_230_);
lean_inc(v_simprocs_229_);
lean_inc(v_ctx_228_);
lean_inc(v_entries_227_);
lean_inc(v_mvarId_226_);
lean_dec(v___x_224_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_240_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = lean_array_push(v_entries_227_, v___x_223_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_mvarId_226_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_ctx_228_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v_simprocs_229_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v_usedTheorems_230_);
lean_ctor_set(v_reuseFailAlloc_239_, 5, v_diag_231_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, sizeof(void*)*6, v_modified_225_);
v___x_237_ = v_reuseFailAlloc_239_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; 
v___x_238_ = lean_st_ref_put(v___y_179_, v___x_237_);
v_a_186_ = v_a_202_;
goto v___jp_185_;
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec(v_a_202_);
lean_dec_ref(v___x_197_);
lean_dec(v_a_196_);
lean_dec_ref_known(v___x_193_, 1);
v_a_241_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_220_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_220_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_197_);
lean_dec(v_a_196_);
lean_dec_ref_known(v___x_193_, 1);
return v___x_201_;
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec_ref_known(v___x_193_, 1);
lean_dec_ref(v_b_178_);
v_a_251_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_195_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_195_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_193_, 1);
v_a_186_ = v_b_178_;
goto v___jp_185_;
}
}
v___jp_185_:
{
size_t v___x_187_; size_t v___x_188_; 
v___x_187_ = ((size_t)1ULL);
v___x_188_ = lean_usize_add(v_i_177_, v___x_187_);
v_i_177_ = v___x_188_;
v_b_178_ = v_a_186_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_174_ = stack[0].m_obj;
lean_object* v_as_175_ = stack[1].m_obj;
size_t v_sz_176_ = stack[2].m_num;
size_t v_i_177_ = stack[3].m_num;
lean_object* v_b_178_ = stack[4].m_obj;
lean_object* v___y_179_ = stack[5].m_obj;
lean_object* v___y_180_ = stack[6].m_obj;
lean_object* v___y_181_ = stack[7].m_obj;
lean_object* v___y_182_ = stack[8].m_obj;
lean_object* v___y_183_ = stack[9].m_obj;
lean_object* v_res_259_;
v_res_259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(v_a_174_, v_as_175_, v_sz_176_, v_i_177_, v_b_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3___boxed(lean_object* v_a_260_, lean_object* v_as_261_, lean_object* v_sz_262_, lean_object* v_i_263_, lean_object* v_b_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
size_t v_sz_boxed_271_; size_t v_i_boxed_272_; lean_object* v_res_273_; 
v_sz_boxed_271_ = lean_unbox_usize(v_sz_262_);
lean_dec(v_sz_262_);
v_i_boxed_272_ = lean_unbox_usize(v_i_263_);
lean_dec(v_i_263_);
v_res_273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(v_a_260_, v_as_261_, v_sz_boxed_271_, v_i_boxed_272_, v_b_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v_as_261_);
lean_dec_ref(v_a_260_);
return v_res_273_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v___f_281_; lean_object* v___x_282_; lean_object* v_mvarId_283_; lean_object* v___x_284_; 
v___f_281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___closed__0));
v___x_282_ = lean_st_ref_get(v_a_275_);
v_mvarId_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_mvarId_283_);
lean_dec(v___x_282_);
v___x_284_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__0___redArg(v_mvarId_283_, v___f_281_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_286_; lean_object* v_mvarId_287_; lean_object* v___x_288_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref_known(v___x_284_, 1);
v___x_286_ = lean_st_ref_get(v_a_275_);
v_mvarId_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_mvarId_287_);
lean_dec(v___x_286_);
v___x_288_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_287_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_290_; lean_object* v_ctx_291_; lean_object* v_simpTheorems_292_; size_t v_sz_293_; size_t v___x_294_; lean_object* v___x_295_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_289_);
lean_dec_ref_known(v___x_288_, 1);
v___x_290_ = lean_st_ref_get(v_a_275_);
v_ctx_291_ = lean_ctor_get(v___x_290_, 2);
lean_inc_ref(v_ctx_291_);
lean_dec(v___x_290_);
v_simpTheorems_292_ = lean_ctor_get(v_ctx_291_, 6);
lean_inc_ref(v_simpTheorems_292_);
lean_dec_ref(v_ctx_291_);
v_sz_293_ = lean_array_size(v_a_285_);
v___x_294_ = ((size_t)0ULL);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_spec__3(v_a_289_, v_a_285_, v_sz_293_, v___x_294_, v_simpTheorems_292_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
lean_dec(v_a_285_);
lean_dec(v_a_289_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_303_; 
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; 
v_unused_304_ = lean_ctor_get(v___x_295_, 0);
lean_dec(v_unused_304_);
v___x_297_ = v___x_295_;
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
else
{
lean_dec(v___x_295_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = lean_box(0);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v_a_305_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_295_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_295_);
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
lean_dec(v_a_285_);
v_a_313_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_288_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_288_);
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
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_a_321_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_284_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_284_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_275_ = stack[0].m_obj;
lean_object* v_a_276_ = stack[1].m_obj;
lean_object* v_a_277_ = stack[2].m_obj;
lean_object* v_a_278_ = stack[3].m_obj;
lean_object* v_a_279_ = stack[4].m_obj;
lean_object* v_res_329_;
v_res_329_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
stack->m_obj
 = v_res_329_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___boxed(lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
return v_res_336_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg(lean_object* v_a_337_){
_start:
{
lean_object* v___x_339_; lean_object* v_ctx_340_; lean_object* v_simpTheorems_341_; lean_object* v___x_342_; 
v___x_339_ = lean_st_ref_get(v_a_337_);
v_ctx_340_ = lean_ctor_get(v___x_339_, 2);
lean_inc_ref(v_ctx_340_);
lean_dec(v___x_339_);
v_simpTheorems_341_ = lean_ctor_get(v_ctx_340_, 6);
lean_inc_ref(v_simpTheorems_341_);
lean_dec_ref(v_ctx_340_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v_simpTheorems_341_);
return v___x_342_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_337_ = stack[0].m_obj;
lean_object* v_res_343_;
v_res_343_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg(v_a_337_);
stack->m_obj
 = v_res_343_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg___boxed(lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___redArg(v_a_344_);
lean_dec(v_a_344_);
return v_res_346_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_353_; lean_object* v_ctx_354_; lean_object* v_simpTheorems_355_; lean_object* v___x_356_; 
v___x_353_ = lean_st_ref_get(v_a_347_);
v_ctx_354_ = lean_ctor_get(v___x_353_, 2);
lean_inc_ref(v_ctx_354_);
lean_dec(v___x_353_);
v_simpTheorems_355_ = lean_ctor_get(v_ctx_354_, 6);
lean_inc_ref(v_simpTheorems_355_);
lean_dec_ref(v_ctx_354_);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v_simpTheorems_355_);
return v___x_356_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_347_ = stack[0].m_obj;
lean_object* v_a_348_ = stack[1].m_obj;
lean_object* v_a_349_ = stack[2].m_obj;
lean_object* v_a_350_ = stack[3].m_obj;
lean_object* v_a_351_ = stack[4].m_obj;
lean_object* v_res_357_;
v_res_357_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___boxed(lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
return v_res_364_;
}
}
lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(lean_object* v___y_365_){
_start:
{
lean_object* v___x_367_; lean_object* v_ngen_368_; lean_object* v_namePrefix_369_; lean_object* v_idx_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_400_; 
v___x_367_ = lean_st_ref_get(v___y_365_);
v_ngen_368_ = lean_ctor_get(v___x_367_, 2);
lean_inc_ref(v_ngen_368_);
lean_dec(v___x_367_);
v_namePrefix_369_ = lean_ctor_get(v_ngen_368_, 0);
v_idx_370_ = lean_ctor_get(v_ngen_368_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v_ngen_368_);
if (v_isSharedCheck_400_ == 0)
{
v___x_372_ = v_ngen_368_;
v_isShared_373_ = v_isSharedCheck_400_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_idx_370_);
lean_inc(v_namePrefix_369_);
lean_dec(v_ngen_368_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_400_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v_r_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
lean_inc(v_idx_370_);
lean_inc(v_namePrefix_369_);
v_r_374_ = l_Lean_Name_num___override(v_namePrefix_369_, v_idx_370_);
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_add(v_idx_370_, v___x_375_);
lean_dec(v_idx_370_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 1, v___x_376_);
v___x_378_ = v___x_372_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_namePrefix_369_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_376_);
v___x_378_ = v_reuseFailAlloc_399_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; lean_object* v_env_380_; lean_object* v_nextMacroScope_381_; lean_object* v_auxDeclNGen_382_; lean_object* v_traceState_383_; lean_object* v_cache_384_; lean_object* v_recordedDeps_385_; lean_object* v_messages_386_; lean_object* v_infoState_387_; lean_object* v_snapshotTasks_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_397_; 
v___x_379_ = lean_st_ref_take(v___y_365_);
v_env_380_ = lean_ctor_get(v___x_379_, 0);
v_nextMacroScope_381_ = lean_ctor_get(v___x_379_, 1);
v_auxDeclNGen_382_ = lean_ctor_get(v___x_379_, 3);
v_traceState_383_ = lean_ctor_get(v___x_379_, 4);
v_cache_384_ = lean_ctor_get(v___x_379_, 5);
v_recordedDeps_385_ = lean_ctor_get(v___x_379_, 6);
v_messages_386_ = lean_ctor_get(v___x_379_, 7);
v_infoState_387_ = lean_ctor_get(v___x_379_, 8);
v_snapshotTasks_388_ = lean_ctor_get(v___x_379_, 9);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_379_, 2);
lean_dec(v_unused_398_);
v___x_390_ = v___x_379_;
v_isShared_391_ = v_isSharedCheck_397_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_snapshotTasks_388_);
lean_inc(v_infoState_387_);
lean_inc(v_messages_386_);
lean_inc(v_recordedDeps_385_);
lean_inc(v_cache_384_);
lean_inc(v_traceState_383_);
lean_inc(v_auxDeclNGen_382_);
lean_inc(v_nextMacroScope_381_);
lean_inc(v_env_380_);
lean_dec(v___x_379_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_397_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 2, v___x_378_);
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_env_380_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_nextMacroScope_381_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_auxDeclNGen_382_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v_traceState_383_);
lean_ctor_set(v_reuseFailAlloc_396_, 5, v_cache_384_);
lean_ctor_set(v_reuseFailAlloc_396_, 6, v_recordedDeps_385_);
lean_ctor_set(v_reuseFailAlloc_396_, 7, v_messages_386_);
lean_ctor_set(v_reuseFailAlloc_396_, 8, v_infoState_387_);
lean_ctor_set(v_reuseFailAlloc_396_, 9, v_snapshotTasks_388_);
v___x_393_ = v_reuseFailAlloc_396_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_st_ref_put(v___y_365_, v___x_393_);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v_r_374_);
return v___x_395_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_365_ = stack[0].m_obj;
lean_object* v_res_401_;
v_res_401_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_365_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg___boxed(lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_402_);
lean_dec(v___y_402_);
return v_res_404_;
}
}
lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0(lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_409_);
return v___x_411_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_405_ = stack[0].m_obj;
lean_object* v___y_406_ = stack[1].m_obj;
lean_object* v___y_407_ = stack[2].m_obj;
lean_object* v___y_408_ = stack[3].m_obj;
lean_object* v___y_409_ = stack[4].m_obj;
lean_object* v_res_412_;
v_res_412_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0(v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
stack->m_obj
 = v_res_412_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___boxed(lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0(v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
return v_res_419_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__0));
v___x_422_ = l_Lean_stringToMessageData(v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__2));
v___x_425_ = l_Lean_stringToMessageData(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__4));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(lean_object* v_x_429_){
_start:
{
switch(lean_obj_tag(v_x_429_))
{
case 0:
{
lean_object* v_declName_431_; uint8_t v_post_432_; uint8_t v_inv_433_; uint8_t v___x_434_; lean_object* v_r_435_; 
v_declName_431_ = lean_ctor_get(v_x_429_, 0);
lean_inc(v_declName_431_);
v_post_432_ = lean_ctor_get_uint8(v_x_429_, sizeof(void*)*1);
v_inv_433_ = lean_ctor_get_uint8(v_x_429_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_x_429_, 1);
v___x_434_ = 0;
v_r_435_ = l_Lean_MessageData_ofConstName(v_declName_431_, v___x_434_);
if (v_post_432_ == 0)
{
if (v_inv_433_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__1);
v___x_437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v_r_435_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__3);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v_r_435_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
else
{
if (v_inv_433_ == 0)
{
lean_object* v___x_442_; 
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v_r_435_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_obj_once(&l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5, &l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5_once, _init_l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___closed__5);
v___x_444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v_r_435_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
}
case 1:
{
lean_object* v_fvarId_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_455_; 
v_fvarId_446_ = lean_ctor_get(v_x_429_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v_x_429_);
if (v_isSharedCheck_455_ == 0)
{
v___x_448_ = v_x_429_;
v_isShared_449_ = v_isSharedCheck_455_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_fvarId_446_);
lean_dec(v_x_429_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_455_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_450_ = l_Lean_mkFVar(v_fvarId_446_);
v___x_451_ = l_Lean_MessageData_ofExpr(v___x_450_);
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 0);
lean_ctor_set(v___x_448_, 0, v___x_451_);
v___x_453_ = v___x_448_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
case 2:
{
lean_object* v_ref_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_ref_456_ = lean_ctor_get(v_x_429_, 1);
lean_inc(v_ref_456_);
lean_dec_ref_known(v_x_429_, 2);
v___x_457_ = l_Lean_MessageData_ofSyntax(v_ref_456_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
default: 
{
lean_object* v_name_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_467_; 
v_name_459_ = lean_ctor_get(v_x_429_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v_x_429_);
if (v_isSharedCheck_467_ == 0)
{
v___x_461_ = v_x_429_;
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_name_459_);
lean_dec(v_x_429_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = l_Lean_MessageData_ofName(v_name_459_);
if (v_isShared_462_ == 0)
{
lean_ctor_set_tag(v___x_461_, 0);
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
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
}
LEAN_EXPORT void l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_429_ = stack[0].m_obj;
lean_object* v_res_468_;
v_res_468_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_x_429_);
stack->m_obj
 = v_res_468_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg___boxed(lean_object* v_x_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_x_469_);
return v_res_471_;
}
}
lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1(lean_object* v_x_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_x_472_);
return v___x_479_;
}
}
LEAN_EXPORT void l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_472_ = stack[0].m_obj;
lean_object* v___y_473_ = stack[1].m_obj;
lean_object* v___y_474_ = stack[2].m_obj;
lean_object* v___y_475_ = stack[3].m_obj;
lean_object* v___y_476_ = stack[4].m_obj;
lean_object* v___y_477_ = stack[5].m_obj;
lean_object* v_res_480_;
v_res_480_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1(v_x_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___boxed(lean_object* v_x_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1(v_x_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
return v_res_488_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(lean_object* v_msgData_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; lean_object* v_env_496_; uint8_t v___x_497_; lean_object* v_env_498_; lean_object* v___x_499_; lean_object* v_toCold_500_; lean_object* v_mctx_501_; lean_object* v_lctx_502_; lean_object* v_options_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_495_ = lean_st_ref_get(v___y_493_);
v_env_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc_ref(v_env_496_);
lean_dec(v___x_495_);
v___x_497_ = 0;
v_env_498_ = l_Lean_Environment_setRecordingDeps(v_env_496_, v___x_497_);
v___x_499_ = lean_st_ref_get(v___y_491_);
v_toCold_500_ = lean_ctor_get(v___y_492_, 0);
v_mctx_501_ = lean_ctor_get(v___x_499_, 0);
lean_inc_ref(v_mctx_501_);
lean_dec(v___x_499_);
v_lctx_502_ = lean_ctor_get(v___y_490_, 2);
v_options_503_ = lean_ctor_get(v_toCold_500_, 2);
lean_inc_ref(v_options_503_);
lean_inc_ref(v_lctx_502_);
v___x_504_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_504_, 0, v_env_498_);
lean_ctor_set(v___x_504_, 1, v_mctx_501_);
lean_ctor_set(v___x_504_, 2, v_lctx_502_);
lean_ctor_set(v___x_504_, 3, v_options_503_);
v___x_505_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v_msgData_489_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_489_ = stack[0].m_obj;
lean_object* v___y_490_ = stack[1].m_obj;
lean_object* v___y_491_ = stack[2].m_obj;
lean_object* v___y_492_ = stack[3].m_obj;
lean_object* v___y_493_ = stack[4].m_obj;
lean_object* v_res_507_;
v_res_507_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msgData_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2___boxed(lean_object* v_msgData_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msgData_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_514_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_515_; double v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = lean_float_of_nat(v___x_515_);
return v___x_516_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(lean_object* v_cls_520_, lean_object* v_msg_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_ref_527_; lean_object* v___x_528_; lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_574_; 
v_ref_527_ = lean_ctor_get(v___y_524_, 2);
v___x_528_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msg_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_574_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_574_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_574_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v_traceState_534_; lean_object* v_env_535_; lean_object* v_nextMacroScope_536_; lean_object* v_ngen_537_; lean_object* v_auxDeclNGen_538_; lean_object* v_cache_539_; lean_object* v_recordedDeps_540_; lean_object* v_messages_541_; lean_object* v_infoState_542_; lean_object* v_snapshotTasks_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_573_; 
v___x_533_ = lean_st_ref_take(v___y_525_);
v_traceState_534_ = lean_ctor_get(v___x_533_, 4);
v_env_535_ = lean_ctor_get(v___x_533_, 0);
v_nextMacroScope_536_ = lean_ctor_get(v___x_533_, 1);
v_ngen_537_ = lean_ctor_get(v___x_533_, 2);
v_auxDeclNGen_538_ = lean_ctor_get(v___x_533_, 3);
v_cache_539_ = lean_ctor_get(v___x_533_, 5);
v_recordedDeps_540_ = lean_ctor_get(v___x_533_, 6);
v_messages_541_ = lean_ctor_get(v___x_533_, 7);
v_infoState_542_ = lean_ctor_get(v___x_533_, 8);
v_snapshotTasks_543_ = lean_ctor_get(v___x_533_, 9);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_573_ == 0)
{
v___x_545_ = v___x_533_;
v_isShared_546_ = v_isSharedCheck_573_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_snapshotTasks_543_);
lean_inc(v_infoState_542_);
lean_inc(v_messages_541_);
lean_inc(v_recordedDeps_540_);
lean_inc(v_cache_539_);
lean_inc(v_traceState_534_);
lean_inc(v_auxDeclNGen_538_);
lean_inc(v_ngen_537_);
lean_inc(v_nextMacroScope_536_);
lean_inc(v_env_535_);
lean_dec(v___x_533_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_573_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
uint64_t v_tid_547_; lean_object* v_traces_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_572_; 
v_tid_547_ = lean_ctor_get_uint64(v_traceState_534_, sizeof(void*)*1);
v_traces_548_ = lean_ctor_get(v_traceState_534_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v_traceState_534_);
if (v_isSharedCheck_572_ == 0)
{
v___x_550_ = v_traceState_534_;
v_isShared_551_ = v_isSharedCheck_572_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_traces_548_);
lean_dec(v_traceState_534_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_572_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; double v___x_554_; uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_552_ = lean_box(0);
v___x_553_ = lean_box(0);
v___x_554_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0);
v___x_555_ = 0;
v___x_556_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1));
v___x_557_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_557_, 0, v_cls_520_);
lean_ctor_set(v___x_557_, 1, v___x_553_);
lean_ctor_set(v___x_557_, 2, v___x_556_);
lean_ctor_set_float(v___x_557_, sizeof(void*)*3, v___x_554_);
lean_ctor_set_float(v___x_557_, sizeof(void*)*3 + 8, v___x_554_);
lean_ctor_set_uint8(v___x_557_, sizeof(void*)*3 + 16, v___x_555_);
v___x_558_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2));
v___x_559_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v_a_529_);
lean_ctor_set(v___x_559_, 2, v___x_558_);
lean_inc(v_ref_527_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v_ref_527_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = l_Lean_PersistentArray_push___redArg(v_traces_548_, v___x_560_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_561_);
v___x_563_ = v___x_550_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_561_);
lean_ctor_set_uint64(v_reuseFailAlloc_571_, sizeof(void*)*1, v_tid_547_);
v___x_563_ = v_reuseFailAlloc_571_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_565_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 4, v___x_563_);
v___x_565_ = v___x_545_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_env_535_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_nextMacroScope_536_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v_ngen_537_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v_auxDeclNGen_538_);
lean_ctor_set(v_reuseFailAlloc_570_, 4, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_570_, 5, v_cache_539_);
lean_ctor_set(v_reuseFailAlloc_570_, 6, v_recordedDeps_540_);
lean_ctor_set(v_reuseFailAlloc_570_, 7, v_messages_541_);
lean_ctor_set(v_reuseFailAlloc_570_, 8, v_infoState_542_);
lean_ctor_set(v_reuseFailAlloc_570_, 9, v_snapshotTasks_543_);
v___x_565_ = v_reuseFailAlloc_570_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = lean_st_ref_put(v___y_525_, v___x_565_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_552_);
v___x_568_ = v___x_531_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_552_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_520_ = stack[0].m_obj;
lean_object* v_msg_521_ = stack[1].m_obj;
lean_object* v___y_522_ = stack[2].m_obj;
lean_object* v___y_523_ = stack[3].m_obj;
lean_object* v___y_524_ = stack[4].m_obj;
lean_object* v___y_525_ = stack[5].m_obj;
lean_object* v_res_575_;
v_res_575_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_cls_520_, v_msg_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
stack->m_obj
 = v_res_575_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___boxed(lean_object* v_cls_576_, lean_object* v_msg_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_cls_576_, v_msg_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
return v_res_583_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(lean_object* v_fvarId_584_, lean_object* v_fst_585_, lean_object* v_snd_586_, lean_object* v___x_587_, uint8_t v___x_588_, lean_object* v___x_589_, lean_object* v_a_590_, lean_object* v___x_591_, lean_object* v_userName_592_, lean_object* v_origType_593_, lean_object* v_____r_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; lean_object* v_ctx_602_; lean_object* v_simpTheorems_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_601_ = lean_st_ref_get(v___y_595_);
v_ctx_602_ = lean_ctor_get(v___x_601_, 2);
lean_inc_ref(v_ctx_602_);
lean_dec(v___x_601_);
v_simpTheorems_603_ = lean_ctor_get(v_ctx_602_, 6);
lean_inc_ref(v_simpTheorems_603_);
lean_dec_ref(v_ctx_602_);
lean_inc(v_fvarId_584_);
v___x_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_604_, 0, v_fvarId_584_);
v___x_605_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(v_simpTheorems_603_, v___x_604_);
v___x_606_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_599_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
lean_inc_ref(v_snd_586_);
lean_inc_ref(v_fst_585_);
v___x_608_ = l_Lean_Meta_mkExpectedTypeHint(v_fst_585_, v_snd_586_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v_indexConfig_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v_indexConfig_610_ = lean_ctor_get(v___x_587_, 5);
v___x_611_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_611_, 0, v_a_607_);
lean_inc_ref(v_indexConfig_610_);
lean_inc_ref(v___x_611_);
v___x_612_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v___x_605_, v___x_611_, v_a_609_, v_indexConfig_610_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_644_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_644_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_644_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_644_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v_mvarId_618_; lean_object* v_entries_619_; lean_object* v_simprocs_620_; lean_object* v_usedTheorems_621_; lean_object* v_diag_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_642_; 
v___x_617_ = lean_st_ref_take(v___y_595_);
v_mvarId_618_ = lean_ctor_get(v___x_617_, 0);
v_entries_619_ = lean_ctor_get(v___x_617_, 1);
v_simprocs_620_ = lean_ctor_get(v___x_617_, 3);
v_usedTheorems_621_ = lean_ctor_get(v___x_617_, 4);
v_diag_622_ = lean_ctor_get(v___x_617_, 5);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; 
v_unused_643_ = lean_ctor_get(v___x_617_, 2);
lean_dec(v_unused_643_);
v___x_624_ = v___x_617_;
v_isShared_625_ = v_isSharedCheck_642_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_diag_622_);
lean_inc(v_usedTheorems_621_);
lean_inc(v_simprocs_620_);
lean_inc(v_entries_619_);
lean_inc(v_mvarId_618_);
lean_dec(v___x_617_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_642_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___y_627_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_array_get_size(v_entries_619_);
v___x_638_ = lean_nat_dec_lt(v_a_590_, v___x_637_);
if (v___x_638_ == 0)
{
lean_dec_ref_known(v___x_611_, 1);
lean_dec_ref(v_origType_593_);
lean_dec(v_userName_592_);
lean_dec_ref(v_snd_586_);
lean_dec_ref(v_fst_585_);
lean_dec(v_fvarId_584_);
v___y_627_ = v_entries_619_;
goto v___jp_626_;
}
else
{
lean_object* v_xs_x27_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_xs_x27_639_ = lean_array_fset(v_entries_619_, v_a_590_, v___x_591_);
v___x_640_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_640_, 0, v_fvarId_584_);
lean_ctor_set(v___x_640_, 1, v_userName_592_);
lean_ctor_set(v___x_640_, 2, v___x_611_);
lean_ctor_set(v___x_640_, 3, v_origType_593_);
lean_ctor_set(v___x_640_, 4, v_snd_586_);
lean_ctor_set(v___x_640_, 5, v_fst_585_);
v___x_641_ = lean_array_fset(v_xs_x27_639_, v_a_590_, v___x_640_);
v___y_627_ = v___x_641_;
goto v___jp_626_;
}
v___jp_626_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_628_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v___x_587_, v_a_613_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 2, v___x_628_);
lean_ctor_set(v___x_624_, 1, v___y_627_);
v___x_630_ = v___x_624_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_mvarId_618_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v___y_627_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_simprocs_620_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_usedTheorems_621_);
lean_ctor_set(v_reuseFailAlloc_636_, 5, v_diag_622_);
v___x_630_ = v_reuseFailAlloc_636_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*6, v___x_588_);
v___x_631_ = lean_st_ref_put(v___y_595_, v___x_630_);
v___x_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_589_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_632_);
v___x_634_ = v___x_615_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
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
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref_known(v___x_611_, 1);
lean_dec_ref(v_origType_593_);
lean_dec(v_userName_592_);
lean_dec_ref(v___x_589_);
lean_dec_ref(v___x_587_);
lean_dec_ref(v_snd_586_);
lean_dec_ref(v_fst_585_);
lean_dec(v_fvarId_584_);
v_a_645_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_612_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_612_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_a_607_);
lean_dec_ref(v___x_605_);
lean_dec_ref(v_origType_593_);
lean_dec(v_userName_592_);
lean_dec_ref(v___x_589_);
lean_dec_ref(v___x_587_);
lean_dec_ref(v_snd_586_);
lean_dec_ref(v_fst_585_);
lean_dec(v_fvarId_584_);
v_a_653_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_608_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_608_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec_ref(v___x_605_);
lean_dec_ref(v_origType_593_);
lean_dec(v_userName_592_);
lean_dec_ref(v___x_589_);
lean_dec_ref(v___x_587_);
lean_dec_ref(v_snd_586_);
lean_dec_ref(v_fst_585_);
lean_dec(v_fvarId_584_);
v_a_661_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_606_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_606_);
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
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_584_ = stack[0].m_obj;
lean_object* v_fst_585_ = stack[1].m_obj;
lean_object* v_snd_586_ = stack[2].m_obj;
lean_object* v___x_587_ = stack[3].m_obj;
uint8_t v___x_588_ = stack[4].m_num;
lean_object* v___x_589_ = stack[5].m_obj;
lean_object* v_a_590_ = stack[6].m_obj;
lean_object* v___x_591_ = stack[7].m_obj;
lean_object* v_userName_592_ = stack[8].m_obj;
lean_object* v_origType_593_ = stack[9].m_obj;
lean_object* v_____r_594_ = stack[10].m_obj;
lean_object* v___y_595_ = stack[11].m_obj;
lean_object* v___y_596_ = stack[12].m_obj;
lean_object* v___y_597_ = stack[13].m_obj;
lean_object* v___y_598_ = stack[14].m_obj;
lean_object* v___y_599_ = stack[15].m_obj;
lean_object* v_res_669_;
v_res_669_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fvarId_584_, v_fst_585_, v_snd_586_, v___x_587_, v___x_588_, v___x_589_, v_a_590_, v___x_591_, v_userName_592_, v_origType_593_, v_____r_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
stack->m_obj
 = v_res_669_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_fvarId_670_ = _args[0];
lean_object* v_fst_671_ = _args[1];
lean_object* v_snd_672_ = _args[2];
lean_object* v___x_673_ = _args[3];
lean_object* v___x_674_ = _args[4];
lean_object* v___x_675_ = _args[5];
lean_object* v_a_676_ = _args[6];
lean_object* v___x_677_ = _args[7];
lean_object* v_userName_678_ = _args[8];
lean_object* v_origType_679_ = _args[9];
lean_object* v_____r_680_ = _args[10];
lean_object* v___y_681_ = _args[11];
lean_object* v___y_682_ = _args[12];
lean_object* v___y_683_ = _args[13];
lean_object* v___y_684_ = _args[14];
lean_object* v___y_685_ = _args[15];
lean_object* v___y_686_ = _args[16];
_start:
{
uint8_t v___x_25153__boxed_687_; lean_object* v_res_688_; 
v___x_25153__boxed_687_ = lean_unbox(v___x_674_);
v_res_688_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fvarId_670_, v_fst_671_, v_snd_672_, v___x_673_, v___x_25153__boxed_687_, v___x_675_, v_a_676_, v___x_677_, v_userName_678_, v_origType_679_, v_____r_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec(v_a_676_);
return v_res_688_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_705_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__7));
v___x_706_ = l_Lean_Name_append(v___x_705_, v___x_704_);
return v___x_706_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__9));
v___x_709_ = l_Lean_stringToMessageData(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__11));
v___x_712_ = l_Lean_stringToMessageData(v___x_711_);
return v___x_712_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__13));
v___x_715_ = l_Lean_stringToMessageData(v___x_714_);
return v___x_715_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(lean_object* v_upperBound_716_, lean_object* v___x_717_, lean_object* v___x_718_, lean_object* v_a_719_, lean_object* v_b_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_a_728_; lean_object* v___y_733_; uint8_t v___x_752_; 
v___x_752_ = lean_nat_dec_lt(v_a_719_, v_upperBound_716_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
lean_dec(v_a_719_);
lean_dec_ref(v___x_718_);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v_b_720_);
return v___x_753_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_ctx_759_; lean_object* v___x_760_; lean_object* v_ctx_761_; lean_object* v_simpTheorems_762_; lean_object* v_fvarId_763_; lean_object* v_userName_764_; lean_object* v_id_765_; lean_object* v_origType_766_; lean_object* v_type_767_; lean_object* v_proof_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v_mvarId_773_; lean_object* v_usedTheorems_774_; lean_object* v_diag_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec_ref(v_b_720_);
v___x_754_ = lean_box(0);
v___x_755_ = lean_box(0);
v___x_756_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0));
v___x_757_ = lean_array_fget_borrowed(v___x_717_, v_a_719_);
v___x_758_ = lean_st_ref_get(v___y_721_);
v_ctx_759_ = lean_ctor_get(v___x_758_, 2);
lean_inc_ref(v_ctx_759_);
lean_dec(v___x_758_);
v___x_760_ = lean_st_ref_get(v___y_721_);
v_ctx_761_ = lean_ctor_get(v___x_760_, 2);
lean_inc_ref(v_ctx_761_);
lean_dec(v___x_760_);
v_simpTheorems_762_ = lean_ctor_get(v_ctx_761_, 6);
lean_inc_ref(v_simpTheorems_762_);
lean_dec_ref(v_ctx_761_);
v_fvarId_763_ = lean_ctor_get(v___x_757_, 0);
v_userName_764_ = lean_ctor_get(v___x_757_, 1);
v_id_765_ = lean_ctor_get(v___x_757_, 2);
v_origType_766_ = lean_ctor_get(v___x_757_, 3);
v_type_767_ = lean_ctor_get(v___x_757_, 4);
v_proof_768_ = lean_ctor_get(v___x_757_, 5);
lean_inc_ref(v_id_765_);
v___x_769_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(v_simpTheorems_762_, v_id_765_);
v___x_770_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v_ctx_759_, v___x_769_);
v___x_771_ = lean_st_ref_get(v___y_721_);
v___x_772_ = lean_st_ref_get(v___y_721_);
v_mvarId_773_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_mvarId_773_);
lean_dec(v___x_771_);
v_usedTheorems_774_ = lean_ctor_get(v___x_772_, 4);
lean_inc_ref(v_usedTheorems_774_);
v_diag_775_ = lean_ctor_get(v___x_772_, 5);
lean_inc_ref(v_diag_775_);
lean_dec(v___x_772_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_usedTheorems_774_);
lean_ctor_set(v___x_776_, 1, v_diag_775_);
lean_inc_ref(v___x_718_);
lean_inc_ref(v___x_770_);
lean_inc_ref(v_type_767_);
lean_inc_ref(v_proof_768_);
v___x_777_ = l_Lean_Meta_simpStep(v_mvarId_773_, v_proof_768_, v_type_767_, v___x_770_, v___x_718_, v___x_755_, v___x_752_, v___x_776_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec_ref_known(v___x_776_, 2);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_870_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_870_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_870_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_870_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v_fst_782_; lean_object* v_snd_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_869_; 
v_fst_782_ = lean_ctor_get(v_a_778_, 0);
v_snd_783_ = lean_ctor_get(v_a_778_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v_a_778_);
if (v_isSharedCheck_869_ == 0)
{
v___x_785_ = v_a_778_;
v_isShared_786_ = v_isSharedCheck_869_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_snd_783_);
lean_inc(v_fst_782_);
lean_dec(v_a_778_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_869_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; uint8_t v_modified_788_; lean_object* v_mvarId_789_; lean_object* v_entries_790_; lean_object* v_ctx_791_; lean_object* v_simprocs_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_866_; 
v___x_787_ = lean_st_ref_take(v___y_721_);
v_modified_788_ = lean_ctor_get_uint8(v___x_787_, sizeof(void*)*6);
v_mvarId_789_ = lean_ctor_get(v___x_787_, 0);
v_entries_790_ = lean_ctor_get(v___x_787_, 1);
v_ctx_791_ = lean_ctor_get(v___x_787_, 2);
v_simprocs_792_ = lean_ctor_get(v___x_787_, 3);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; lean_object* v_unused_868_; 
v_unused_867_ = lean_ctor_get(v___x_787_, 5);
lean_dec(v_unused_867_);
v_unused_868_ = lean_ctor_get(v___x_787_, 4);
lean_dec(v_unused_868_);
v___x_794_ = v___x_787_;
v_isShared_795_ = v_isSharedCheck_866_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_simprocs_792_);
lean_inc(v_ctx_791_);
lean_inc(v_entries_790_);
lean_inc(v_mvarId_789_);
lean_dec(v___x_787_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_866_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_usedTheorems_796_; lean_object* v_diag_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_865_; 
v_usedTheorems_796_ = lean_ctor_get(v_snd_783_, 0);
v_diag_797_ = lean_ctor_get(v_snd_783_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v_snd_783_);
if (v_isSharedCheck_865_ == 0)
{
v___x_799_ = v_snd_783_;
v_isShared_800_ = v_isSharedCheck_865_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_diag_797_);
lean_inc(v_usedTheorems_796_);
lean_dec(v_snd_783_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_865_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 5, v_diag_797_);
lean_ctor_set(v___x_794_, 4, v_usedTheorems_796_);
v___x_802_ = v___x_794_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_mvarId_789_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_entries_790_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v_ctx_791_);
lean_ctor_set(v_reuseFailAlloc_864_, 3, v_simprocs_792_);
lean_ctor_set(v_reuseFailAlloc_864_, 4, v_usedTheorems_796_);
lean_ctor_set(v_reuseFailAlloc_864_, 5, v_diag_797_);
lean_ctor_set_uint8(v_reuseFailAlloc_864_, sizeof(void*)*6, v_modified_788_);
v___x_802_ = v_reuseFailAlloc_864_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; 
v___x_803_ = lean_st_ref_put(v___y_721_, v___x_802_);
if (lean_obj_tag(v_fst_782_) == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
lean_del_object(v___x_799_);
lean_dec_ref(v___x_770_);
lean_dec(v_a_719_);
lean_dec_ref(v___x_718_);
v___x_804_ = lean_box(v___x_752_);
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v___x_754_);
lean_ctor_set(v___x_785_, 0, v___x_805_);
v___x_807_ = v___x_785_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_754_);
v___x_807_ = v_reuseFailAlloc_811_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_809_; 
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_807_);
v___x_809_ = v___x_780_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
else
{
lean_object* v_val_812_; lean_object* v_fst_813_; lean_object* v_snd_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_863_; 
lean_del_object(v___x_785_);
lean_del_object(v___x_780_);
v_val_812_ = lean_ctor_get(v_fst_782_, 0);
lean_inc(v_val_812_);
lean_dec_ref_known(v_fst_782_, 1);
v_fst_813_ = lean_ctor_get(v_val_812_, 0);
v_snd_814_ = lean_ctor_get(v_val_812_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_val_812_);
if (v_isSharedCheck_863_ == 0)
{
v___x_816_ = v_val_812_;
v_isShared_817_ = v_isSharedCheck_863_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_snd_814_);
lean_inc(v_fst_813_);
lean_dec(v_val_812_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_863_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
uint8_t v___x_818_; 
v___x_818_ = lean_expr_eqv(v_snd_814_, v_type_767_);
if (v___x_818_ == 0)
{
lean_object* v_toCold_819_; lean_object* v_options_820_; lean_object* v_inheritedTraceOptions_821_; uint8_t v_hasTrace_822_; 
v_toCold_819_ = lean_ctor_get(v___y_724_, 0);
v_options_820_ = lean_ctor_get(v_toCold_819_, 2);
v_inheritedTraceOptions_821_ = lean_ctor_get(v_toCold_819_, 11);
v_hasTrace_822_ = lean_ctor_get_uint8(v_options_820_, sizeof(void*)*1);
if (v_hasTrace_822_ == 0)
{
lean_del_object(v___x_816_);
lean_del_object(v___x_799_);
goto v___jp_823_;
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_825_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_826_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8);
v___x_827_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_821_, v_options_820_, v___x_826_);
if (v___x_827_ == 0)
{
lean_del_object(v___x_816_);
lean_del_object(v___x_799_);
goto v___jp_823_;
}
else
{
lean_object* v___x_828_; 
lean_inc_ref(v_id_765_);
v___x_828_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_id_765_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_828_, 1);
v___x_830_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10);
if (v_isShared_817_ == 0)
{
lean_ctor_set_tag(v___x_816_, 7);
lean_ctor_set(v___x_816_, 1, v_a_829_);
lean_ctor_set(v___x_816_, 0, v___x_830_);
v___x_832_ = v___x_816_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_a_829_);
v___x_832_ = v_reuseFailAlloc_854_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12);
if (v_isShared_800_ == 0)
{
lean_ctor_set_tag(v___x_799_, 7);
lean_ctor_set(v___x_799_, 1, v___x_833_);
lean_ctor_set(v___x_799_, 0, v___x_832_);
v___x_835_ = v___x_799_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_833_);
v___x_835_ = v_reuseFailAlloc_853_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_inc_ref(v_type_767_);
v___x_836_ = l_Lean_MessageData_ofExpr(v_type_767_);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14);
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
lean_inc(v_snd_814_);
v___x_840_ = l_Lean_MessageData_ofExpr(v_snd_814_);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v___x_825_, v___x_841_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_844_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
lean_inc_ref(v_origType_766_);
lean_inc(v_userName_764_);
lean_inc(v_fvarId_763_);
v___x_844_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fvarId_763_, v_fst_813_, v_snd_814_, v___x_770_, v___x_752_, v___x_756_, v_a_719_, v___x_754_, v_userName_764_, v_origType_766_, v_a_843_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
v___y_733_ = v___x_844_;
goto v___jp_732_;
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec(v_snd_814_);
lean_dec(v_fst_813_);
lean_dec_ref(v___x_770_);
lean_dec(v_a_719_);
lean_dec_ref(v___x_718_);
v_a_845_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_842_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_842_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_del_object(v___x_816_);
lean_dec(v_snd_814_);
lean_dec(v_fst_813_);
lean_del_object(v___x_799_);
lean_dec_ref(v___x_770_);
lean_dec(v_a_719_);
lean_dec_ref(v___x_718_);
v_a_855_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_828_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_828_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
v___jp_823_:
{
lean_object* v___x_824_; 
lean_inc_ref(v_origType_766_);
lean_inc(v_userName_764_);
lean_inc(v_fvarId_763_);
v___x_824_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fvarId_763_, v_fst_813_, v_snd_814_, v___x_770_, v___x_752_, v___x_756_, v_a_719_, v___x_754_, v_userName_764_, v_origType_766_, v___x_754_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
v___y_733_ = v___x_824_;
goto v___jp_732_;
}
}
else
{
lean_del_object(v___x_816_);
lean_dec(v_snd_814_);
lean_dec(v_fst_813_);
lean_del_object(v___x_799_);
lean_dec_ref(v___x_770_);
v_a_728_ = v___x_756_;
goto v___jp_727_;
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
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec_ref(v___x_770_);
lean_dec(v_a_719_);
lean_dec_ref(v___x_718_);
v_a_871_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_777_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_777_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
v___jp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_nat_add(v_a_719_, v___x_729_);
lean_dec(v_a_719_);
v_a_719_ = v___x_730_;
v_b_720_ = v_a_728_;
goto _start;
}
v___jp_732_:
{
if (lean_obj_tag(v___y_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_743_; 
v_a_734_ = lean_ctor_get(v___y_733_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___y_733_);
if (v_isSharedCheck_743_ == 0)
{
v___x_736_ = v___y_733_;
v_isShared_737_ = v_isSharedCheck_743_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___y_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_743_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
if (lean_obj_tag(v_a_734_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; 
lean_dec(v_a_719_);
lean_dec_ref(v___x_718_);
v_a_738_ = lean_ctor_get(v_a_734_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v_a_734_, 1);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v_a_738_);
v___x_740_ = v___x_736_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
else
{
lean_object* v_a_742_; 
lean_del_object(v___x_736_);
v_a_742_ = lean_ctor_get(v_a_734_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v_a_734_, 1);
v_a_728_ = v_a_742_;
goto v___jp_727_;
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_a_719_);
lean_dec_ref(v___x_718_);
v_a_744_ = lean_ctor_get(v___y_733_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___y_733_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___y_733_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___y_733_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_716_ = stack[0].m_obj;
lean_object* v___x_717_ = stack[1].m_obj;
lean_object* v___x_718_ = stack[2].m_obj;
lean_object* v_a_719_ = stack[3].m_obj;
lean_object* v_b_720_ = stack[4].m_obj;
lean_object* v___y_721_ = stack[5].m_obj;
lean_object* v___y_722_ = stack[6].m_obj;
lean_object* v___y_723_ = stack[7].m_obj;
lean_object* v___y_724_ = stack[8].m_obj;
lean_object* v___y_725_ = stack[9].m_obj;
lean_object* v_res_879_;
v_res_879_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_upperBound_716_, v___x_717_, v___x_718_, v_a_719_, v_b_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
stack->m_obj
 = v_res_879_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___boxed(lean_object* v_upperBound_880_, lean_object* v___x_881_, lean_object* v___x_882_, lean_object* v_a_883_, lean_object* v_b_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_upperBound_880_, v___x_881_, v___x_882_, v_a_883_, v_b_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___x_881_);
lean_dec(v_upperBound_880_);
return v_res_891_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___x_909_; lean_object* v_mvarId_910_; lean_object* v_entries_911_; lean_object* v_ctx_912_; lean_object* v_simprocs_913_; lean_object* v_usedTheorems_914_; lean_object* v_diag_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_1022_; 
v___x_909_ = lean_st_ref_take(v_a_892_);
v_mvarId_910_ = lean_ctor_get(v___x_909_, 0);
v_entries_911_ = lean_ctor_get(v___x_909_, 1);
v_ctx_912_ = lean_ctor_get(v___x_909_, 2);
v_simprocs_913_ = lean_ctor_get(v___x_909_, 3);
v_usedTheorems_914_ = lean_ctor_get(v___x_909_, 4);
v_diag_915_ = lean_ctor_get(v___x_909_, 5);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_917_ = v___x_909_;
v_isShared_918_ = v_isSharedCheck_1022_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_diag_915_);
lean_inc(v_usedTheorems_914_);
lean_inc(v_simprocs_913_);
lean_inc(v_ctx_912_);
lean_inc(v_entries_911_);
lean_inc(v_mvarId_910_);
lean_dec(v___x_909_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_1022_;
goto v_resetjp_916_;
}
v___jp_898_:
{
lean_object* v___x_904_; uint8_t v_modified_905_; 
v___x_904_ = lean_st_ref_get(v___y_899_);
v_modified_905_ = lean_ctor_get_uint8(v___x_904_, sizeof(void*)*6);
lean_dec(v___x_904_);
if (v_modified_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_box(v_modified_905_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
else
{
v_a_892_ = v___y_899_;
v_a_893_ = v___y_900_;
v_a_894_ = v___y_901_;
v_a_895_ = v___y_902_;
v_a_896_ = v___y_903_;
goto _start;
}
}
v_resetjp_916_:
{
uint8_t v___x_919_; lean_object* v___x_921_; 
v___x_919_ = 0;
if (v_isShared_918_ == 0)
{
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_mvarId_910_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_entries_911_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_ctx_912_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v_simprocs_913_);
lean_ctor_set(v_reuseFailAlloc_1021_, 4, v_usedTheorems_914_);
lean_ctor_set(v_reuseFailAlloc_1021_, 5, v_diag_915_);
v___x_921_ = v_reuseFailAlloc_1021_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_simprocs_924_; lean_object* v___x_925_; lean_object* v_entries_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
lean_ctor_set_uint8(v___x_921_, sizeof(void*)*6, v___x_919_);
v___x_922_ = lean_st_ref_put(v_a_892_, v___x_921_);
v___x_923_ = lean_st_ref_get(v_a_892_);
v_simprocs_924_ = lean_ctor_get(v___x_923_, 3);
lean_inc_ref_n(v_simprocs_924_, 2);
lean_dec(v___x_923_);
v___x_925_ = lean_st_ref_get(v_a_892_);
v_entries_926_ = lean_ctor_get(v___x_925_, 1);
lean_inc_ref(v_entries_926_);
lean_dec(v___x_925_);
v___x_927_ = lean_array_get_size(v_entries_926_);
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_box(0);
v___x_930_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0));
v___x_931_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v___x_927_, v_entries_926_, v_simprocs_924_, v___x_928_, v___x_930_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
lean_dec_ref(v_entries_926_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_1012_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_934_ = v___x_931_;
v_isShared_935_ = v_isSharedCheck_1012_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_1012_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_fst_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_1010_; 
v_fst_936_ = lean_ctor_get(v_a_932_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_a_932_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v_a_932_, 1);
lean_dec(v_unused_1011_);
v___x_938_ = v_a_932_;
v_isShared_939_ = v_isSharedCheck_1010_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_fst_936_);
lean_dec(v_a_932_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_1010_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
if (lean_obj_tag(v_fst_936_) == 0)
{
lean_object* v___x_940_; lean_object* v_mvarId_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_ctx_944_; lean_object* v_usedTheorems_945_; lean_object* v_diag_946_; uint8_t v___x_947_; lean_object* v___x_949_; 
lean_del_object(v___x_934_);
v___x_940_ = lean_st_ref_get(v_a_892_);
v_mvarId_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_mvarId_941_);
lean_dec(v___x_940_);
v___x_942_ = lean_st_ref_get(v_a_892_);
v___x_943_ = lean_st_ref_get(v_a_892_);
v_ctx_944_ = lean_ctor_get(v___x_942_, 2);
lean_inc_ref(v_ctx_944_);
lean_dec(v___x_942_);
v_usedTheorems_945_ = lean_ctor_get(v___x_943_, 4);
lean_inc_ref(v_usedTheorems_945_);
v_diag_946_ = lean_ctor_get(v___x_943_, 5);
lean_inc_ref(v_diag_946_);
lean_dec(v___x_943_);
v___x_947_ = 1;
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v_diag_946_);
lean_ctor_set(v___x_938_, 0, v_usedTheorems_945_);
v___x_949_ = v___x_938_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_usedTheorems_945_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_diag_946_);
v___x_949_ = v_reuseFailAlloc_1005_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; 
lean_inc(v_mvarId_941_);
v___x_950_ = l_Lean_Meta_simpTarget(v_mvarId_941_, v_ctx_944_, v_simprocs_924_, v___x_929_, v___x_947_, v___x_949_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_996_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_996_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_996_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_996_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_fst_955_; lean_object* v_snd_956_; lean_object* v___x_957_; uint8_t v_modified_958_; lean_object* v_mvarId_959_; lean_object* v_entries_960_; lean_object* v_ctx_961_; lean_object* v_simprocs_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_993_; 
v_fst_955_ = lean_ctor_get(v_a_951_, 0);
lean_inc(v_fst_955_);
v_snd_956_ = lean_ctor_get(v_a_951_, 1);
lean_inc(v_snd_956_);
lean_dec(v_a_951_);
v___x_957_ = lean_st_ref_take(v_a_892_);
v_modified_958_ = lean_ctor_get_uint8(v___x_957_, sizeof(void*)*6);
v_mvarId_959_ = lean_ctor_get(v___x_957_, 0);
v_entries_960_ = lean_ctor_get(v___x_957_, 1);
v_ctx_961_ = lean_ctor_get(v___x_957_, 2);
v_simprocs_962_ = lean_ctor_get(v___x_957_, 3);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; lean_object* v_unused_995_; 
v_unused_994_ = lean_ctor_get(v___x_957_, 5);
lean_dec(v_unused_994_);
v_unused_995_ = lean_ctor_get(v___x_957_, 4);
lean_dec(v_unused_995_);
v___x_964_ = v___x_957_;
v_isShared_965_ = v_isSharedCheck_993_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_simprocs_962_);
lean_inc(v_ctx_961_);
lean_inc(v_entries_960_);
lean_inc(v_mvarId_959_);
lean_dec(v___x_957_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_993_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_usedTheorems_966_; lean_object* v_diag_967_; lean_object* v___x_969_; 
v_usedTheorems_966_ = lean_ctor_get(v_snd_956_, 0);
lean_inc_ref(v_usedTheorems_966_);
v_diag_967_ = lean_ctor_get(v_snd_956_, 1);
lean_inc_ref(v_diag_967_);
lean_dec(v_snd_956_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 5, v_diag_967_);
lean_ctor_set(v___x_964_, 4, v_usedTheorems_966_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_mvarId_959_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_entries_960_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_ctx_961_);
lean_ctor_set(v_reuseFailAlloc_992_, 3, v_simprocs_962_);
lean_ctor_set(v_reuseFailAlloc_992_, 4, v_usedTheorems_966_);
lean_ctor_set(v_reuseFailAlloc_992_, 5, v_diag_967_);
lean_ctor_set_uint8(v_reuseFailAlloc_992_, sizeof(void*)*6, v_modified_958_);
v___x_969_ = v_reuseFailAlloc_992_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; 
v___x_970_ = lean_st_ref_put(v_a_892_, v___x_969_);
if (lean_obj_tag(v_fst_955_) == 0)
{
lean_object* v___x_971_; lean_object* v___x_973_; 
lean_dec(v_mvarId_941_);
v___x_971_ = lean_box(v___x_947_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_971_);
v___x_973_ = v___x_953_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
else
{
lean_object* v_val_975_; uint8_t v___x_976_; 
lean_del_object(v___x_953_);
v_val_975_ = lean_ctor_get(v_fst_955_, 0);
lean_inc(v_val_975_);
lean_dec_ref_known(v_fst_955_, 1);
v___x_976_ = l_Lean_instBEqMVarId_beq(v_mvarId_941_, v_val_975_);
lean_dec(v_mvarId_941_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v_entries_978_; lean_object* v_ctx_979_; lean_object* v_simprocs_980_; lean_object* v_usedTheorems_981_; lean_object* v_diag_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_990_; 
v___x_977_ = lean_st_ref_take(v_a_892_);
v_entries_978_ = lean_ctor_get(v___x_977_, 1);
v_ctx_979_ = lean_ctor_get(v___x_977_, 2);
v_simprocs_980_ = lean_ctor_get(v___x_977_, 3);
v_usedTheorems_981_ = lean_ctor_get(v___x_977_, 4);
v_diag_982_ = lean_ctor_get(v___x_977_, 5);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v___x_977_, 0);
lean_dec(v_unused_991_);
v___x_984_ = v___x_977_;
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_diag_982_);
lean_inc(v_usedTheorems_981_);
lean_inc(v_simprocs_980_);
lean_inc(v_ctx_979_);
lean_inc(v_entries_978_);
lean_dec(v___x_977_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_990_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v_val_975_);
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_val_975_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_entries_978_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_ctx_979_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v_simprocs_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v_usedTheorems_981_);
lean_ctor_set(v_reuseFailAlloc_989_, 5, v_diag_982_);
v___x_987_ = v_reuseFailAlloc_989_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; 
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*6, v___x_947_);
v___x_988_ = lean_st_ref_put(v_a_892_, v___x_987_);
v___y_899_ = v_a_892_;
v___y_900_ = v_a_893_;
v___y_901_ = v_a_894_;
v___y_902_ = v_a_895_;
v___y_903_ = v_a_896_;
goto v___jp_898_;
}
}
}
else
{
lean_dec(v_val_975_);
v___y_899_ = v_a_892_;
v___y_900_ = v_a_893_;
v___y_901_ = v_a_894_;
v___y_902_ = v_a_895_;
v___y_903_ = v_a_896_;
goto v___jp_898_;
}
}
}
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_mvarId_941_);
v_a_997_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_950_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_950_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1008_; 
lean_del_object(v___x_938_);
lean_dec_ref(v_simprocs_924_);
v_val_1006_ = lean_ctor_get(v_fst_936_, 0);
lean_inc(v_val_1006_);
lean_dec_ref_known(v_fst_936_, 1);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v_val_1006_);
v___x_1008_ = v___x_934_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_val_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v_simprocs_924_);
v_a_1013_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_931_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_931_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_892_ = stack[0].m_obj;
lean_object* v_a_893_ = stack[1].m_obj;
lean_object* v_a_894_ = stack[2].m_obj;
lean_object* v_a_895_ = stack[3].m_obj;
lean_object* v_a_896_ = stack[4].m_obj;
lean_object* v_res_1023_;
v_res_1023_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
stack->m_obj
 = v_res_1023_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___boxed(lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
return v_res_1030_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(lean_object* v_cls_1031_, lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_cls_1031_, v_msg_1032_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
return v___x_1039_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1031_ = stack[0].m_obj;
lean_object* v_msg_1032_ = stack[1].m_obj;
lean_object* v___y_1033_ = stack[2].m_obj;
lean_object* v___y_1034_ = stack[3].m_obj;
lean_object* v___y_1035_ = stack[4].m_obj;
lean_object* v___y_1036_ = stack[5].m_obj;
lean_object* v___y_1037_ = stack[6].m_obj;
lean_object* v_res_1040_;
v_res_1040_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(v_cls_1031_, v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
stack->m_obj
 = v_res_1040_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___boxed(lean_object* v_cls_1041_, lean_object* v_msg_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(v_cls_1041_, v_msg_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
return v_res_1049_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(lean_object* v_upperBound_1050_, lean_object* v___x_1051_, lean_object* v___x_1052_, lean_object* v_inst_1053_, lean_object* v_R_1054_, lean_object* v_a_1055_, lean_object* v_b_1056_, lean_object* v_c_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_upperBound_1050_, v___x_1051_, v___x_1052_, v_a_1055_, v_b_1056_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1050_ = stack[0].m_obj;
lean_object* v___x_1051_ = stack[1].m_obj;
lean_object* v___x_1052_ = stack[2].m_obj;
lean_object* v_a_1055_ = stack[5].m_obj;
lean_object* v_b_1056_ = stack[6].m_obj;
lean_object* v___y_1058_ = stack[8].m_obj;
lean_object* v___y_1059_ = stack[9].m_obj;
lean_object* v___y_1060_ = stack[10].m_obj;
lean_object* v___y_1061_ = stack[11].m_obj;
lean_object* v___y_1062_ = stack[12].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(v_upperBound_1050_, v___x_1051_, v___x_1052_, lean_box(0), lean_box(0), v_a_1055_, v_b_1056_, lean_box(0), v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___boxed(lean_object* v_upperBound_1066_, lean_object* v___x_1067_, lean_object* v___x_1068_, lean_object* v_inst_1069_, lean_object* v_R_1070_, lean_object* v_a_1071_, lean_object* v_b_1072_, lean_object* v_c_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(v_upperBound_1066_, v___x_1067_, v___x_1068_, v_inst_1069_, v_R_1070_, v_a_1071_, v_b_1072_, v_c_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___x_1067_);
lean_dec(v_upperBound_1066_);
return v_res_1080_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(lean_object* v_as_1081_, size_t v_sz_1082_, size_t v_i_1083_, lean_object* v_b_1084_){
_start:
{
lean_object* v_a_1087_; uint8_t v___x_1091_; 
v___x_1091_ = lean_usize_dec_lt(v_i_1083_, v_sz_1082_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_b_1084_);
return v___x_1092_;
}
else
{
lean_object* v_snd_1093_; lean_object* v_fst_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1131_; 
v_snd_1093_ = lean_ctor_get(v_b_1084_, 1);
v_fst_1094_ = lean_ctor_get(v_b_1084_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_b_1084_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1096_ = v_b_1084_;
v_isShared_1097_ = v_isSharedCheck_1131_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_snd_1093_);
lean_inc(v_fst_1094_);
lean_dec(v_b_1084_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1131_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_fst_1098_; lean_object* v_snd_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1130_; 
v_fst_1098_ = lean_ctor_get(v_snd_1093_, 0);
v_snd_1099_ = lean_ctor_get(v_snd_1093_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_snd_1093_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1101_ = v_snd_1093_;
v_isShared_1102_ = v_isSharedCheck_1130_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_snd_1099_);
lean_inc(v_fst_1098_);
lean_dec(v_snd_1093_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1130_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_a_1103_; lean_object* v_fvarId_1104_; lean_object* v_userName_1105_; lean_object* v_origType_1106_; lean_object* v_type_1107_; lean_object* v_proof_1108_; uint8_t v___x_1122_; 
v_a_1103_ = lean_array_uget_borrowed(v_as_1081_, v_i_1083_);
v_fvarId_1104_ = lean_ctor_get(v_a_1103_, 0);
v_userName_1105_ = lean_ctor_get(v_a_1103_, 1);
v_origType_1106_ = lean_ctor_get(v_a_1103_, 3);
v_type_1107_ = lean_ctor_get(v_a_1103_, 4);
v_proof_1108_ = lean_ctor_get(v_a_1103_, 5);
lean_inc_ref(v_type_1107_);
v___x_1122_ = l_Lean_Expr_isTrue(v_type_1107_);
if (v___x_1122_ == 0)
{
uint8_t v___x_1123_; 
v___x_1123_ = lean_unbox(v_snd_1099_);
if (v___x_1123_ == 0)
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_expr_eqv(v_type_1107_, v_origType_1106_);
if (v___x_1124_ == 0)
{
lean_dec(v_snd_1099_);
goto v___jp_1109_;
}
else
{
if (v___x_1122_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_del_object(v___x_1101_);
lean_del_object(v___x_1096_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v_fst_1098_);
lean_ctor_set(v___x_1125_, 1, v_snd_1099_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v_fst_1094_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v_a_1087_ = v___x_1126_;
goto v___jp_1086_;
}
else
{
lean_dec(v_snd_1099_);
goto v___jp_1109_;
}
}
}
else
{
lean_dec(v_snd_1099_);
goto v___jp_1109_;
}
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_del_object(v___x_1101_);
lean_del_object(v___x_1096_);
lean_inc(v_fvarId_1104_);
v___x_1127_ = lean_array_push(v_fst_1098_, v_fvarId_1104_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v_snd_1099_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v_fst_1094_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v_a_1087_ = v___x_1129_;
goto v___jp_1086_;
}
v___jp_1109_:
{
lean_object* v___x_1110_; uint8_t v___x_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
lean_inc(v_fvarId_1104_);
v___x_1110_ = lean_array_push(v_fst_1098_, v_fvarId_1104_);
v___x_1111_ = 0;
v___x_1112_ = 0;
lean_inc_ref(v_proof_1108_);
lean_inc_ref(v_type_1107_);
lean_inc(v_userName_1105_);
v___x_1113_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1113_, 0, v_userName_1105_);
lean_ctor_set(v___x_1113_, 1, v_type_1107_);
lean_ctor_set(v___x_1113_, 2, v_proof_1108_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*3, v___x_1111_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*3 + 1, v___x_1112_);
v___x_1114_ = lean_array_push(v_fst_1094_, v___x_1113_);
v___x_1115_ = lean_box(v___x_1091_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v___x_1115_);
lean_ctor_set(v___x_1101_, 0, v___x_1110_);
v___x_1117_ = v___x_1101_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v___x_1117_);
lean_ctor_set(v___x_1096_, 0, v___x_1114_);
v___x_1119_ = v___x_1096_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
v_a_1087_ = v___x_1119_;
goto v___jp_1086_;
}
}
}
}
}
}
v___jp_1086_:
{
size_t v___x_1088_; size_t v___x_1089_; 
v___x_1088_ = ((size_t)1ULL);
v___x_1089_ = lean_usize_add(v_i_1083_, v___x_1088_);
v_i_1083_ = v___x_1089_;
v_b_1084_ = v_a_1087_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1081_ = stack[0].m_obj;
size_t v_sz_1082_ = stack[1].m_num;
size_t v_i_1083_ = stack[2].m_num;
lean_object* v_b_1084_ = stack[3].m_obj;
lean_object* v_res_1132_;
v_res_1132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_as_1081_, v_sz_1082_, v_i_1083_, v_b_1084_);
stack->m_obj
 = v_res_1132_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg___boxed(lean_object* v_as_1133_, lean_object* v_sz_1134_, lean_object* v_i_1135_, lean_object* v_b_1136_, lean_object* v___y_1137_){
_start:
{
size_t v_sz_boxed_1138_; size_t v_i_boxed_1139_; lean_object* v_res_1140_; 
v_sz_boxed_1138_ = lean_unbox_usize(v_sz_1134_);
lean_dec(v_sz_1134_);
v_i_boxed_1139_ = lean_unbox_usize(v_i_1135_);
lean_dec(v_i_1135_);
v_res_1140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_as_1133_, v_sz_boxed_1138_, v_i_boxed_1139_, v_b_1136_);
lean_dec_ref(v_as_1133_);
return v_res_1140_;
}
}
lean_object* l_Lean_Meta_SimpAll_main(lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v___x_1150_; 
lean_dec_ref_known(v___x_1149_, 1);
v___x_1150_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1211_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1211_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1211_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_unbox(v_a_1151_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v_mvarId_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_entries_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; size_t v_sz_1163_; size_t v___x_1164_; lean_object* v___x_1165_; 
lean_del_object(v___x_1153_);
v___x_1156_ = lean_st_ref_get(v_a_1143_);
v_mvarId_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_mvarId_1157_);
lean_dec(v___x_1156_);
v___x_1158_ = ((lean_object*)(l_Lean_Meta_SimpAll_main___closed__0));
v___x_1159_ = lean_st_ref_get(v_a_1143_);
v_entries_1160_ = lean_ctor_get(v___x_1159_, 1);
lean_inc_ref(v_entries_1160_);
lean_dec(v___x_1159_);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1158_);
lean_ctor_set(v___x_1161_, 1, v_a_1151_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1158_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v_sz_1163_ = lean_array_size(v_entries_1160_);
v___x_1164_ = ((size_t)0ULL);
v___x_1165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_entries_1160_, v_sz_1163_, v___x_1164_, v___x_1162_);
lean_dec_ref(v_entries_1160_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v_snd_1167_; lean_object* v_fst_1168_; lean_object* v_fst_1169_; lean_object* v___x_1170_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v_snd_1167_ = lean_ctor_get(v_a_1166_, 1);
lean_inc(v_snd_1167_);
v_fst_1168_ = lean_ctor_get(v_a_1166_, 0);
lean_inc(v_fst_1168_);
lean_dec(v_a_1166_);
v_fst_1169_ = lean_ctor_get(v_snd_1167_, 0);
lean_inc(v_fst_1169_);
lean_dec(v_snd_1167_);
v___x_1170_ = l_Lean_MVarId_assertHypotheses(v_mvarId_1157_, v_fst_1168_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v_snd_1172_; lean_object* v___x_1173_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v_snd_1172_ = lean_ctor_get(v_a_1171_, 1);
lean_inc(v_snd_1172_);
lean_dec(v_a_1171_);
v___x_1173_ = l_Lean_MVarId_tryClearMany(v_snd_1172_, v_fst_1169_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_fst_1169_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1182_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1178_, 0, v_a_1174_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v___x_1178_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_a_1183_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1173_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1173_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec(v_fst_1169_);
v_a_1191_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1170_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1170_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec(v_mvarId_1157_);
v_a_1199_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1165_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1165_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
lean_dec(v_a_1151_);
v___x_1207_ = lean_box(0);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1207_);
v___x_1209_ = v___x_1153_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
v_a_1212_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1150_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1150_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
v_a_1220_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1149_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1149_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_SimpAll_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1143_ = stack[0].m_obj;
lean_object* v_a_1144_ = stack[1].m_obj;
lean_object* v_a_1145_ = stack[2].m_obj;
lean_object* v_a_1146_ = stack[3].m_obj;
lean_object* v_a_1147_ = stack[4].m_obj;
lean_object* v_res_1228_;
v_res_1228_ = l_Lean_Meta_SimpAll_main(v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
stack->m_obj
 = v_res_1228_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_main___boxed(lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Meta_SimpAll_main(v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
return v_res_1235_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(lean_object* v_as_1236_, size_t v_sz_1237_, size_t v_i_1238_, lean_object* v_b_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_as_1236_, v_sz_1237_, v_i_1238_, v_b_1239_);
return v___x_1246_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1236_ = stack[0].m_obj;
size_t v_sz_1237_ = stack[1].m_num;
size_t v_i_1238_ = stack[2].m_num;
lean_object* v_b_1239_ = stack[3].m_obj;
lean_object* v___y_1240_ = stack[4].m_obj;
lean_object* v___y_1241_ = stack[5].m_obj;
lean_object* v___y_1242_ = stack[6].m_obj;
lean_object* v___y_1243_ = stack[7].m_obj;
lean_object* v___y_1244_ = stack[8].m_obj;
lean_object* v_res_1247_;
v_res_1247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(v_as_1236_, v_sz_1237_, v_i_1238_, v_b_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
stack->m_obj
 = v_res_1247_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___boxed(lean_object* v_as_1248_, lean_object* v_sz_1249_, lean_object* v_i_1250_, lean_object* v_b_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
size_t v_sz_boxed_1258_; size_t v_i_boxed_1259_; lean_object* v_res_1260_; 
v_sz_boxed_1258_ = lean_unbox_usize(v_sz_1249_);
lean_dec(v_sz_1249_);
v_i_boxed_1259_ = lean_unbox_usize(v_i_1250_);
lean_dec(v_i_1250_);
v_res_1260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(v_as_1248_, v_sz_boxed_1258_, v_i_boxed_1259_, v_b_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v_as_1248_);
return v_res_1260_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(lean_object* v_mvarId_1261_, lean_object* v_x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1261_, v_x_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
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
v_a_1277_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1268_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1268_);
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1261_ = stack[0].m_obj;
lean_object* v_x_1262_ = stack[1].m_obj;
lean_object* v___y_1263_ = stack[2].m_obj;
lean_object* v___y_1264_ = stack[3].m_obj;
lean_object* v___y_1265_ = stack[4].m_obj;
lean_object* v___y_1266_ = stack[5].m_obj;
lean_object* v_res_1285_;
v_res_1285_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1261_, v_x_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
stack->m_obj
 = v_res_1285_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg___boxed(lean_object* v_mvarId_1286_, lean_object* v_x_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1286_, v_x_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
return v_res_1293_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(lean_object* v_00_u03b1_1294_, lean_object* v_mvarId_1295_, lean_object* v_x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1295_, v_x_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1295_ = stack[1].m_obj;
lean_object* v_x_1296_ = stack[2].m_obj;
lean_object* v___y_1297_ = stack[3].m_obj;
lean_object* v___y_1298_ = stack[4].m_obj;
lean_object* v___y_1299_ = stack[5].m_obj;
lean_object* v___y_1300_ = stack[6].m_obj;
lean_object* v_res_1303_;
v_res_1303_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(lean_box(0), v_mvarId_1295_, v_x_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
stack->m_obj
 = v_res_1303_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___boxed(lean_object* v_00_u03b1_1304_, lean_object* v_mvarId_1305_, lean_object* v_x_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(v_00_u03b1_1304_, v_mvarId_1305_, v_x_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
return v_res_1312_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(lean_object* v_msg_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_ref_1319_; lean_object* v___x_1320_; lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1329_; 
v_ref_1319_ = lean_ctor_get(v___y_1316_, 2);
v___x_1320_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msg_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
lean_inc(v_ref_1319_);
v___x_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1325_, 0, v_ref_1319_);
lean_ctor_set(v___x_1325_, 1, v_a_1321_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set_tag(v___x_1323_, 1);
lean_ctor_set(v___x_1323_, 0, v___x_1325_);
v___x_1327_ = v___x_1323_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1313_ = stack[0].m_obj;
lean_object* v___y_1314_ = stack[1].m_obj;
lean_object* v___y_1315_ = stack[2].m_obj;
lean_object* v___y_1316_ = stack[3].m_obj;
lean_object* v___y_1317_ = stack[4].m_obj;
lean_object* v_res_1330_;
v_res_1330_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v_msg_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
stack->m_obj
 = v_res_1330_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg___boxed(lean_object* v_msg_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v_msg_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
return v_res_1337_;
}
}
static lean_object* _init_l_Lean_Meta_simpAll___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l_Lean_Meta_simpAll___lam__0___closed__0));
v___x_1340_ = l_Lean_stringToMessageData(v___x_1339_);
return v___x_1340_;
}
}
lean_object* l_Lean_Meta_simpAll___lam__0(lean_object* v___x_1341_, lean_object* v_ctx_1342_, lean_object* v_mvarId_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_st_mk_ref(v___x_1341_);
v___x_1350_ = l_Lean_Meta_SimpAll_main(v___x_1349_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1378_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1378_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1378_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_st_ref_get(v___x_1349_);
lean_dec(v___x_1349_);
if (lean_obj_tag(v_a_1351_) == 1)
{
lean_object* v_config_1364_; uint8_t v_failIfUnchanged_1365_; 
v_config_1364_ = lean_ctor_get(v_ctx_1342_, 0);
v_failIfUnchanged_1365_ = lean_ctor_get_uint8(v_config_1364_, sizeof(void*)*3 + 13);
if (v_failIfUnchanged_1365_ == 0)
{
goto v___jp_1356_;
}
else
{
lean_object* v_val_1366_; uint8_t v___x_1367_; 
v_val_1366_ = lean_ctor_get(v_a_1351_, 0);
v___x_1367_ = l_Lean_instBEqMVarId_beq(v_mvarId_1343_, v_val_1366_);
if (v___x_1367_ == 0)
{
goto v___jp_1356_;
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref_known(v_a_1351_, 1);
lean_dec(v___x_1355_);
lean_del_object(v___x_1353_);
v___x_1368_ = lean_obj_once(&l_Lean_Meta_simpAll___lam__0___closed__1, &l_Lean_Meta_simpAll___lam__0___closed__1_once, _init_l_Lean_Meta_simpAll___lam__0___closed__1);
v___x_1369_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v___x_1368_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
else
{
goto v___jp_1356_;
}
v___jp_1356_:
{
lean_object* v_usedTheorems_1357_; lean_object* v_diag_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v_usedTheorems_1357_ = lean_ctor_get(v___x_1355_, 4);
lean_inc_ref(v_usedTheorems_1357_);
v_diag_1358_ = lean_ctor_get(v___x_1355_, 5);
lean_inc_ref(v_diag_1358_);
lean_dec(v___x_1355_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_usedTheorems_1357_);
lean_ctor_set(v___x_1359_, 1, v_diag_1358_);
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v_a_1351_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1360_);
v___x_1362_ = v___x_1353_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v___x_1349_);
v_a_1379_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1350_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1350_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
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
LEAN_EXPORT void l_Lean_Meta_simpAll___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1341_ = stack[0].m_obj;
lean_object* v_ctx_1342_ = stack[1].m_obj;
lean_object* v_mvarId_1343_ = stack[2].m_obj;
lean_object* v___y_1344_ = stack[3].m_obj;
lean_object* v___y_1345_ = stack[4].m_obj;
lean_object* v___y_1346_ = stack[5].m_obj;
lean_object* v___y_1347_ = stack[6].m_obj;
lean_object* v_res_1387_;
v_res_1387_ = l_Lean_Meta_simpAll___lam__0(v___x_1341_, v_ctx_1342_, v_mvarId_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
stack->m_obj
 = v_res_1387_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___lam__0___boxed(lean_object* v___x_1388_, lean_object* v_ctx_1389_, lean_object* v_mvarId_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Meta_simpAll___lam__0(v___x_1388_, v_ctx_1389_, v_mvarId_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v_mvarId_1390_);
lean_dec_ref(v_ctx_1389_);
return v_res_1396_;
}
}
lean_object* l_Lean_Meta_simpAll(lean_object* v_mvarId_1399_, lean_object* v_ctx_1400_, lean_object* v_simprocs_1401_, lean_object* v_stats_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_usedTheorems_1408_; lean_object* v_diag_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___f_1413_; lean_object* v___x_1414_; 
v_usedTheorems_1408_ = lean_ctor_get(v_stats_1402_, 0);
v_diag_1409_ = lean_ctor_get(v_stats_1402_, 1);
v___x_1410_ = 0;
v___x_1411_ = ((lean_object*)(l_Lean_Meta_simpAll___closed__0));
lean_inc_ref(v_diag_1409_);
lean_inc_ref(v_usedTheorems_1408_);
lean_inc_ref(v_ctx_1400_);
lean_inc_n(v_mvarId_1399_, 2);
v___x_1412_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1412_, 0, v_mvarId_1399_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
lean_ctor_set(v___x_1412_, 2, v_ctx_1400_);
lean_ctor_set(v___x_1412_, 3, v_simprocs_1401_);
lean_ctor_set(v___x_1412_, 4, v_usedTheorems_1408_);
lean_ctor_set(v___x_1412_, 5, v_diag_1409_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*6, v___x_1410_);
v___f_1413_ = lean_alloc_closure((void*)(l_Lean_Meta_simpAll___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1413_, 0, v___x_1412_);
lean_closure_set(v___f_1413_, 1, v_ctx_1400_);
lean_closure_set(v___f_1413_, 2, v_mvarId_1399_);
v___x_1414_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1399_, v___f_1413_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
return v___x_1414_;
}
}
LEAN_EXPORT void l_Lean_Meta_simpAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1399_ = stack[0].m_obj;
lean_object* v_ctx_1400_ = stack[1].m_obj;
lean_object* v_simprocs_1401_ = stack[2].m_obj;
lean_object* v_stats_1402_ = stack[3].m_obj;
lean_object* v_a_1403_ = stack[4].m_obj;
lean_object* v_a_1404_ = stack[5].m_obj;
lean_object* v_a_1405_ = stack[6].m_obj;
lean_object* v_a_1406_ = stack[7].m_obj;
lean_object* v_res_1415_;
v_res_1415_ = l_Lean_Meta_simpAll(v_mvarId_1399_, v_ctx_1400_, v_simprocs_1401_, v_stats_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
stack->m_obj
 = v_res_1415_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___boxed(lean_object* v_mvarId_1416_, lean_object* v_ctx_1417_, lean_object* v_simprocs_1418_, lean_object* v_stats_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Meta_simpAll(v_mvarId_1416_, v_ctx_1417_, v_simprocs_1418_, v_stats_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec_ref(v_stats_1419_);
return v_res_1425_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(lean_object* v_00_u03b1_1426_, lean_object* v_msg_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v_msg_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1427_ = stack[1].m_obj;
lean_object* v___y_1428_ = stack[2].m_obj;
lean_object* v___y_1429_ = stack[3].m_obj;
lean_object* v___y_1430_ = stack[4].m_obj;
lean_object* v___y_1431_ = stack[5].m_obj;
lean_object* v_res_1434_;
v_res_1434_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(lean_box(0), v_msg_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
stack->m_obj
 = v_res_1434_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_msg_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(v_00_u03b1_1435_, v_msg_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
return v_res_1442_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1512_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_1513_ = 0;
v___x_1514_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_));
v___x_1515_ = l_Lean_registerTraceClass(v___x_1512_, v___x_1513_, v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1516_;
v_res_1516_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1516_;
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
