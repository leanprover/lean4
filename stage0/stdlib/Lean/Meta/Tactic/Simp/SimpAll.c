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
lean_object* v___x_479_; lean_object* v_env_480_; uint8_t v___x_481_; lean_object* v_env_482_; lean_object* v___x_483_; lean_object* v_toCold_484_; lean_object* v_mctx_485_; lean_object* v_lctx_486_; lean_object* v_options_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_479_ = lean_st_ref_get(v___y_477_);
v_env_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc_ref(v_env_480_);
lean_dec(v___x_479_);
v___x_481_ = 0;
v_env_482_ = l_Lean_Environment_setRecordingDeps(v_env_480_, v___x_481_);
v___x_483_ = lean_st_ref_get(v___y_475_);
v_toCold_484_ = lean_ctor_get(v___y_476_, 0);
v_mctx_485_ = lean_ctor_get(v___x_483_, 0);
lean_inc_ref(v_mctx_485_);
lean_dec(v___x_483_);
v_lctx_486_ = lean_ctor_get(v___y_474_, 2);
v_options_487_ = lean_ctor_get(v_toCold_484_, 2);
lean_inc_ref(v_options_487_);
lean_inc_ref(v_lctx_486_);
v___x_488_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_488_, 0, v_env_482_);
lean_ctor_set(v___x_488_, 1, v_mctx_485_);
lean_ctor_set(v___x_488_, 2, v_lctx_486_);
lean_ctor_set(v___x_488_, 3, v_options_487_);
v___x_489_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v_msgData_473_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2___boxed(lean_object* v_msgData_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msgData_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
return v_res_497_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_498_; double v___x_499_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_float_of_nat(v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(lean_object* v_cls_503_, lean_object* v_msg_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_ref_510_; lean_object* v___x_511_; lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_557_; 
v_ref_510_ = lean_ctor_get(v___y_507_, 2);
v___x_511_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msg_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_557_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_557_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_557_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v_traceState_517_; lean_object* v_env_518_; lean_object* v_nextMacroScope_519_; lean_object* v_ngen_520_; lean_object* v_auxDeclNGen_521_; lean_object* v_cache_522_; lean_object* v_recordedDeps_523_; lean_object* v_messages_524_; lean_object* v_infoState_525_; lean_object* v_snapshotTasks_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_556_; 
v___x_516_ = lean_st_ref_take(v___y_508_);
v_traceState_517_ = lean_ctor_get(v___x_516_, 4);
v_env_518_ = lean_ctor_get(v___x_516_, 0);
v_nextMacroScope_519_ = lean_ctor_get(v___x_516_, 1);
v_ngen_520_ = lean_ctor_get(v___x_516_, 2);
v_auxDeclNGen_521_ = lean_ctor_get(v___x_516_, 3);
v_cache_522_ = lean_ctor_get(v___x_516_, 5);
v_recordedDeps_523_ = lean_ctor_get(v___x_516_, 6);
v_messages_524_ = lean_ctor_get(v___x_516_, 7);
v_infoState_525_ = lean_ctor_get(v___x_516_, 8);
v_snapshotTasks_526_ = lean_ctor_get(v___x_516_, 9);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_556_ == 0)
{
v___x_528_ = v___x_516_;
v_isShared_529_ = v_isSharedCheck_556_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_snapshotTasks_526_);
lean_inc(v_infoState_525_);
lean_inc(v_messages_524_);
lean_inc(v_recordedDeps_523_);
lean_inc(v_cache_522_);
lean_inc(v_traceState_517_);
lean_inc(v_auxDeclNGen_521_);
lean_inc(v_ngen_520_);
lean_inc(v_nextMacroScope_519_);
lean_inc(v_env_518_);
lean_dec(v___x_516_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_556_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
uint64_t v_tid_530_; lean_object* v_traces_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_555_; 
v_tid_530_ = lean_ctor_get_uint64(v_traceState_517_, sizeof(void*)*1);
v_traces_531_ = lean_ctor_get(v_traceState_517_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v_traceState_517_);
if (v_isSharedCheck_555_ == 0)
{
v___x_533_ = v_traceState_517_;
v_isShared_534_ = v_isSharedCheck_555_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_traces_531_);
lean_dec(v_traceState_517_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_555_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; double v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_535_ = lean_box(0);
v___x_536_ = lean_box(0);
v___x_537_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0);
v___x_538_ = 0;
v___x_539_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1));
v___x_540_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_540_, 0, v_cls_503_);
lean_ctor_set(v___x_540_, 1, v___x_536_);
lean_ctor_set(v___x_540_, 2, v___x_539_);
lean_ctor_set_float(v___x_540_, sizeof(void*)*3, v___x_537_);
lean_ctor_set_float(v___x_540_, sizeof(void*)*3 + 8, v___x_537_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*3 + 16, v___x_538_);
v___x_541_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2));
v___x_542_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v_a_512_);
lean_ctor_set(v___x_542_, 2, v___x_541_);
lean_inc(v_ref_510_);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v_ref_510_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l_Lean_PersistentArray_push___redArg(v_traces_531_, v___x_543_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_544_);
v___x_546_ = v___x_533_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_544_);
lean_ctor_set_uint64(v_reuseFailAlloc_554_, sizeof(void*)*1, v_tid_530_);
v___x_546_ = v_reuseFailAlloc_554_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_548_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 4, v___x_546_);
v___x_548_ = v___x_528_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_env_518_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_nextMacroScope_519_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_ngen_520_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_auxDeclNGen_521_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_553_, 5, v_cache_522_);
lean_ctor_set(v_reuseFailAlloc_553_, 6, v_recordedDeps_523_);
lean_ctor_set(v_reuseFailAlloc_553_, 7, v_messages_524_);
lean_ctor_set(v_reuseFailAlloc_553_, 8, v_infoState_525_);
lean_ctor_set(v_reuseFailAlloc_553_, 9, v_snapshotTasks_526_);
v___x_548_ = v_reuseFailAlloc_553_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_st_ref_put(v___y_508_, v___x_548_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_535_);
v___x_551_ = v___x_514_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_535_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___boxed(lean_object* v_cls_558_, lean_object* v_msg_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_cls_558_, v_msg_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(lean_object* v_fvarId_566_, lean_object* v_fst_567_, lean_object* v_snd_568_, lean_object* v___x_569_, uint8_t v___x_570_, lean_object* v___x_571_, lean_object* v_a_572_, lean_object* v___x_573_, lean_object* v_userName_574_, lean_object* v_origType_575_, lean_object* v_____r_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; lean_object* v_ctx_584_; lean_object* v_simpTheorems_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_583_ = lean_st_ref_get(v___y_577_);
v_ctx_584_ = lean_ctor_get(v___x_583_, 2);
lean_inc_ref(v_ctx_584_);
lean_dec(v___x_583_);
v_simpTheorems_585_ = lean_ctor_get(v_ctx_584_, 6);
lean_inc_ref(v_simpTheorems_585_);
lean_dec_ref(v_ctx_584_);
lean_inc(v_fvarId_566_);
v___x_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_586_, 0, v_fvarId_566_);
v___x_587_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(v_simpTheorems_585_, v___x_586_);
v___x_588_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_581_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
lean_inc_ref(v_snd_568_);
lean_inc_ref(v_fst_567_);
v___x_590_ = l_Lean_Meta_mkExpectedTypeHint(v_fst_567_, v_snd_568_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v_indexConfig_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v_indexConfig_592_ = lean_ctor_get(v___x_569_, 5);
v___x_593_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_593_, 0, v_a_589_);
lean_inc_ref(v_indexConfig_592_);
lean_inc_ref(v___x_593_);
v___x_594_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v___x_587_, v___x_593_, v_a_591_, v_indexConfig_592_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_626_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_626_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_626_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_626_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v_mvarId_600_; lean_object* v_entries_601_; lean_object* v_simprocs_602_; lean_object* v_usedTheorems_603_; lean_object* v_diag_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_624_; 
v___x_599_ = lean_st_ref_take(v___y_577_);
v_mvarId_600_ = lean_ctor_get(v___x_599_, 0);
v_entries_601_ = lean_ctor_get(v___x_599_, 1);
v_simprocs_602_ = lean_ctor_get(v___x_599_, 3);
v_usedTheorems_603_ = lean_ctor_get(v___x_599_, 4);
v_diag_604_ = lean_ctor_get(v___x_599_, 5);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v___x_599_, 2);
lean_dec(v_unused_625_);
v___x_606_ = v___x_599_;
v_isShared_607_ = v_isSharedCheck_624_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_diag_604_);
lean_inc(v_usedTheorems_603_);
lean_inc(v_simprocs_602_);
lean_inc(v_entries_601_);
lean_inc(v_mvarId_600_);
lean_dec(v___x_599_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_624_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___y_609_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = lean_array_get_size(v_entries_601_);
v___x_620_ = lean_nat_dec_lt(v_a_572_, v___x_619_);
if (v___x_620_ == 0)
{
lean_dec_ref_known(v___x_593_, 1);
lean_dec_ref(v_origType_575_);
lean_dec(v_userName_574_);
lean_dec_ref(v_snd_568_);
lean_dec_ref(v_fst_567_);
lean_dec(v_fvarId_566_);
v___y_609_ = v_entries_601_;
goto v___jp_608_;
}
else
{
lean_object* v_xs_x27_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_xs_x27_621_ = lean_array_fset(v_entries_601_, v_a_572_, v___x_573_);
v___x_622_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_622_, 0, v_fvarId_566_);
lean_ctor_set(v___x_622_, 1, v_userName_574_);
lean_ctor_set(v___x_622_, 2, v___x_593_);
lean_ctor_set(v___x_622_, 3, v_origType_575_);
lean_ctor_set(v___x_622_, 4, v_snd_568_);
lean_ctor_set(v___x_622_, 5, v_fst_567_);
v___x_623_ = lean_array_fset(v_xs_x27_621_, v_a_572_, v___x_622_);
v___y_609_ = v___x_623_;
goto v___jp_608_;
}
v___jp_608_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v___x_569_, v_a_595_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 2, v___x_610_);
lean_ctor_set(v___x_606_, 1, v___y_609_);
v___x_612_ = v___x_606_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_mvarId_600_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___y_609_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_simprocs_602_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v_usedTheorems_603_);
lean_ctor_set(v_reuseFailAlloc_618_, 5, v_diag_604_);
v___x_612_ = v_reuseFailAlloc_618_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*6, v___x_570_);
v___x_613_ = lean_st_ref_put(v___y_577_, v___x_612_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_571_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_614_);
v___x_616_ = v___x_597_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref_known(v___x_593_, 1);
lean_dec_ref(v_origType_575_);
lean_dec(v_userName_574_);
lean_dec_ref(v___x_571_);
lean_dec_ref(v___x_569_);
lean_dec_ref(v_snd_568_);
lean_dec_ref(v_fst_567_);
lean_dec(v_fvarId_566_);
v_a_627_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_594_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_594_);
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
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec(v_a_589_);
lean_dec_ref(v___x_587_);
lean_dec_ref(v_origType_575_);
lean_dec(v_userName_574_);
lean_dec_ref(v___x_571_);
lean_dec_ref(v___x_569_);
lean_dec_ref(v_snd_568_);
lean_dec_ref(v_fst_567_);
lean_dec(v_fvarId_566_);
v_a_635_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_590_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_590_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec_ref(v___x_587_);
lean_dec_ref(v_origType_575_);
lean_dec(v_userName_574_);
lean_dec_ref(v___x_571_);
lean_dec_ref(v___x_569_);
lean_dec_ref(v_snd_568_);
lean_dec_ref(v_fst_567_);
lean_dec(v_fvarId_566_);
v_a_643_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_588_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_588_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_fvarId_651_ = _args[0];
lean_object* v_fst_652_ = _args[1];
lean_object* v_snd_653_ = _args[2];
lean_object* v___x_654_ = _args[3];
lean_object* v___x_655_ = _args[4];
lean_object* v___x_656_ = _args[5];
lean_object* v_a_657_ = _args[6];
lean_object* v___x_658_ = _args[7];
lean_object* v_userName_659_ = _args[8];
lean_object* v_origType_660_ = _args[9];
lean_object* v_____r_661_ = _args[10];
lean_object* v___y_662_ = _args[11];
lean_object* v___y_663_ = _args[12];
lean_object* v___y_664_ = _args[13];
lean_object* v___y_665_ = _args[14];
lean_object* v___y_666_ = _args[15];
lean_object* v___y_667_ = _args[16];
_start:
{
uint8_t v___x_24985__boxed_668_; lean_object* v_res_669_; 
v___x_24985__boxed_668_ = lean_unbox(v___x_655_);
v_res_669_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fvarId_651_, v_fst_652_, v_snd_653_, v___x_654_, v___x_24985__boxed_668_, v___x_656_, v_a_657_, v___x_658_, v_userName_659_, v_origType_660_, v_____r_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec(v_a_657_);
return v_res_669_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_685_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_686_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__7));
v___x_687_ = l_Lean_Name_append(v___x_686_, v___x_685_);
return v___x_687_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__9));
v___x_690_ = l_Lean_stringToMessageData(v___x_689_);
return v___x_690_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__11));
v___x_693_ = l_Lean_stringToMessageData(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__13));
v___x_696_ = l_Lean_stringToMessageData(v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(lean_object* v_upperBound_697_, lean_object* v___x_698_, lean_object* v___x_699_, lean_object* v_a_700_, lean_object* v_b_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_a_709_; lean_object* v___y_714_; uint8_t v___x_733_; 
v___x_733_ = lean_nat_dec_lt(v_a_700_, v_upperBound_697_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
lean_dec(v_a_700_);
lean_dec_ref(v___x_699_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v_b_701_);
return v___x_734_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_ctx_740_; lean_object* v___x_741_; lean_object* v_ctx_742_; lean_object* v_simpTheorems_743_; lean_object* v_fvarId_744_; lean_object* v_userName_745_; lean_object* v_id_746_; lean_object* v_origType_747_; lean_object* v_type_748_; lean_object* v_proof_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_mvarId_754_; lean_object* v_usedTheorems_755_; lean_object* v_diag_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec_ref(v_b_701_);
v___x_735_ = lean_box(0);
v___x_736_ = lean_box(0);
v___x_737_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0));
v___x_738_ = lean_array_fget_borrowed(v___x_698_, v_a_700_);
v___x_739_ = lean_st_ref_get(v___y_702_);
v_ctx_740_ = lean_ctor_get(v___x_739_, 2);
lean_inc_ref(v_ctx_740_);
lean_dec(v___x_739_);
v___x_741_ = lean_st_ref_get(v___y_702_);
v_ctx_742_ = lean_ctor_get(v___x_741_, 2);
lean_inc_ref(v_ctx_742_);
lean_dec(v___x_741_);
v_simpTheorems_743_ = lean_ctor_get(v_ctx_742_, 6);
lean_inc_ref(v_simpTheorems_743_);
lean_dec_ref(v_ctx_742_);
v_fvarId_744_ = lean_ctor_get(v___x_738_, 0);
v_userName_745_ = lean_ctor_get(v___x_738_, 1);
v_id_746_ = lean_ctor_get(v___x_738_, 2);
v_origType_747_ = lean_ctor_get(v___x_738_, 3);
v_type_748_ = lean_ctor_get(v___x_738_, 4);
v_proof_749_ = lean_ctor_get(v___x_738_, 5);
lean_inc_ref(v_id_746_);
v___x_750_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(v_simpTheorems_743_, v_id_746_);
v___x_751_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v_ctx_740_, v___x_750_);
v___x_752_ = lean_st_ref_get(v___y_702_);
v___x_753_ = lean_st_ref_get(v___y_702_);
v_mvarId_754_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_mvarId_754_);
lean_dec(v___x_752_);
v_usedTheorems_755_ = lean_ctor_get(v___x_753_, 4);
lean_inc_ref(v_usedTheorems_755_);
v_diag_756_ = lean_ctor_get(v___x_753_, 5);
lean_inc_ref(v_diag_756_);
lean_dec(v___x_753_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_usedTheorems_755_);
lean_ctor_set(v___x_757_, 1, v_diag_756_);
lean_inc_ref(v___x_699_);
lean_inc_ref(v___x_751_);
lean_inc_ref(v_type_748_);
lean_inc_ref(v_proof_749_);
v___x_758_ = l_Lean_Meta_simpStep(v_mvarId_754_, v_proof_749_, v_type_748_, v___x_751_, v___x_699_, v___x_736_, v___x_733_, v___x_757_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec_ref_known(v___x_757_, 2);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_851_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_851_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_851_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_851_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_fst_763_; lean_object* v_snd_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_850_; 
v_fst_763_ = lean_ctor_get(v_a_759_, 0);
v_snd_764_ = lean_ctor_get(v_a_759_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_a_759_);
if (v_isSharedCheck_850_ == 0)
{
v___x_766_ = v_a_759_;
v_isShared_767_ = v_isSharedCheck_850_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_snd_764_);
lean_inc(v_fst_763_);
lean_dec(v_a_759_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_850_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; uint8_t v_modified_769_; lean_object* v_mvarId_770_; lean_object* v_entries_771_; lean_object* v_ctx_772_; lean_object* v_simprocs_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_847_; 
v___x_768_ = lean_st_ref_take(v___y_702_);
v_modified_769_ = lean_ctor_get_uint8(v___x_768_, sizeof(void*)*6);
v_mvarId_770_ = lean_ctor_get(v___x_768_, 0);
v_entries_771_ = lean_ctor_get(v___x_768_, 1);
v_ctx_772_ = lean_ctor_get(v___x_768_, 2);
v_simprocs_773_ = lean_ctor_get(v___x_768_, 3);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; lean_object* v_unused_849_; 
v_unused_848_ = lean_ctor_get(v___x_768_, 5);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v___x_768_, 4);
lean_dec(v_unused_849_);
v___x_775_ = v___x_768_;
v_isShared_776_ = v_isSharedCheck_847_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_simprocs_773_);
lean_inc(v_ctx_772_);
lean_inc(v_entries_771_);
lean_inc(v_mvarId_770_);
lean_dec(v___x_768_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_847_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_usedTheorems_777_; lean_object* v_diag_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_846_; 
v_usedTheorems_777_ = lean_ctor_get(v_snd_764_, 0);
v_diag_778_ = lean_ctor_get(v_snd_764_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v_snd_764_);
if (v_isSharedCheck_846_ == 0)
{
v___x_780_ = v_snd_764_;
v_isShared_781_ = v_isSharedCheck_846_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_diag_778_);
lean_inc(v_usedTheorems_777_);
lean_dec(v_snd_764_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_846_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 5, v_diag_778_);
lean_ctor_set(v___x_775_, 4, v_usedTheorems_777_);
v___x_783_ = v___x_775_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_mvarId_770_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_entries_771_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_ctx_772_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v_simprocs_773_);
lean_ctor_set(v_reuseFailAlloc_845_, 4, v_usedTheorems_777_);
lean_ctor_set(v_reuseFailAlloc_845_, 5, v_diag_778_);
lean_ctor_set_uint8(v_reuseFailAlloc_845_, sizeof(void*)*6, v_modified_769_);
v___x_783_ = v_reuseFailAlloc_845_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; 
v___x_784_ = lean_st_ref_put(v___y_702_, v___x_783_);
if (lean_obj_tag(v_fst_763_) == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
lean_del_object(v___x_780_);
lean_dec_ref(v___x_751_);
lean_dec(v_a_700_);
lean_dec_ref(v___x_699_);
v___x_785_ = lean_box(v___x_733_);
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v___x_735_);
lean_ctor_set(v___x_766_, 0, v___x_786_);
v___x_788_ = v___x_766_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_735_);
v___x_788_ = v_reuseFailAlloc_792_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_788_);
v___x_790_ = v___x_761_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
else
{
lean_object* v_val_793_; lean_object* v_fst_794_; lean_object* v_snd_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_844_; 
lean_del_object(v___x_766_);
lean_del_object(v___x_761_);
v_val_793_ = lean_ctor_get(v_fst_763_, 0);
lean_inc(v_val_793_);
lean_dec_ref_known(v_fst_763_, 1);
v_fst_794_ = lean_ctor_get(v_val_793_, 0);
v_snd_795_ = lean_ctor_get(v_val_793_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_val_793_);
if (v_isSharedCheck_844_ == 0)
{
v___x_797_ = v_val_793_;
v_isShared_798_ = v_isSharedCheck_844_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_snd_795_);
lean_inc(v_fst_794_);
lean_dec(v_val_793_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_844_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
uint8_t v___x_799_; 
v___x_799_ = lean_expr_eqv(v_snd_795_, v_type_748_);
if (v___x_799_ == 0)
{
lean_object* v_toCold_800_; lean_object* v_options_801_; lean_object* v_inheritedTraceOptions_802_; uint8_t v_hasTrace_803_; 
v_toCold_800_ = lean_ctor_get(v___y_705_, 0);
v_options_801_ = lean_ctor_get(v_toCold_800_, 2);
v_inheritedTraceOptions_802_ = lean_ctor_get(v_toCold_800_, 11);
v_hasTrace_803_ = lean_ctor_get_uint8(v_options_801_, sizeof(void*)*1);
if (v_hasTrace_803_ == 0)
{
lean_del_object(v___x_797_);
lean_del_object(v___x_780_);
goto v___jp_804_;
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_806_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_807_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8);
v___x_808_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_802_, v_options_801_, v___x_807_);
if (v___x_808_ == 0)
{
lean_del_object(v___x_797_);
lean_del_object(v___x_780_);
goto v___jp_804_;
}
else
{
lean_object* v___x_809_; 
lean_inc_ref(v_id_746_);
v___x_809_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_id_746_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v___x_811_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10);
if (v_isShared_798_ == 0)
{
lean_ctor_set_tag(v___x_797_, 7);
lean_ctor_set(v___x_797_, 1, v_a_810_);
lean_ctor_set(v___x_797_, 0, v___x_811_);
v___x_813_ = v___x_797_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_a_810_);
v___x_813_ = v_reuseFailAlloc_835_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12);
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 7);
lean_ctor_set(v___x_780_, 1, v___x_814_);
lean_ctor_set(v___x_780_, 0, v___x_813_);
v___x_816_ = v___x_780_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v___x_814_);
v___x_816_ = v_reuseFailAlloc_834_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
lean_inc_ref(v_type_748_);
v___x_817_ = l_Lean_MessageData_ofExpr(v_type_748_);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
lean_inc(v_snd_795_);
v___x_821_ = l_Lean_MessageData_ofExpr(v_snd_795_);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v___x_806_, v___x_822_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_825_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
lean_inc_ref(v_origType_747_);
lean_inc(v_userName_745_);
lean_inc(v_fvarId_744_);
v___x_825_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fvarId_744_, v_fst_794_, v_snd_795_, v___x_751_, v___x_733_, v___x_737_, v_a_700_, v___x_735_, v_userName_745_, v_origType_747_, v_a_824_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
v___y_714_ = v___x_825_;
goto v___jp_713_;
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_snd_795_);
lean_dec(v_fst_794_);
lean_dec_ref(v___x_751_);
lean_dec(v_a_700_);
lean_dec_ref(v___x_699_);
v_a_826_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_823_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_823_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_del_object(v___x_797_);
lean_dec(v_snd_795_);
lean_dec(v_fst_794_);
lean_del_object(v___x_780_);
lean_dec_ref(v___x_751_);
lean_dec(v_a_700_);
lean_dec_ref(v___x_699_);
v_a_836_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_809_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_809_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
v___jp_804_:
{
lean_object* v___x_805_; 
lean_inc_ref(v_origType_747_);
lean_inc(v_userName_745_);
lean_inc(v_fvarId_744_);
v___x_805_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fvarId_744_, v_fst_794_, v_snd_795_, v___x_751_, v___x_733_, v___x_737_, v_a_700_, v___x_735_, v_userName_745_, v_origType_747_, v___x_735_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
v___y_714_ = v___x_805_;
goto v___jp_713_;
}
}
else
{
lean_del_object(v___x_797_);
lean_dec(v_snd_795_);
lean_dec(v_fst_794_);
lean_del_object(v___x_780_);
lean_dec_ref(v___x_751_);
v_a_709_ = v___x_737_;
goto v___jp_708_;
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
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v___x_751_);
lean_dec(v_a_700_);
lean_dec_ref(v___x_699_);
v_a_852_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_758_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_758_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
v___jp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = lean_nat_add(v_a_700_, v___x_710_);
lean_dec(v_a_700_);
v_a_700_ = v___x_711_;
v_b_701_ = v_a_709_;
goto _start;
}
v___jp_713_:
{
if (lean_obj_tag(v___y_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_724_; 
v_a_715_ = lean_ctor_get(v___y_714_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___y_714_);
if (v_isSharedCheck_724_ == 0)
{
v___x_717_ = v___y_714_;
v_isShared_718_ = v_isSharedCheck_724_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___y_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_724_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
if (lean_obj_tag(v_a_715_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; 
lean_dec(v_a_700_);
lean_dec_ref(v___x_699_);
v_a_719_ = lean_ctor_get(v_a_715_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v_a_715_, 1);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v_a_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
else
{
lean_object* v_a_723_; 
lean_del_object(v___x_717_);
v_a_723_ = lean_ctor_get(v_a_715_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v_a_715_, 1);
v_a_709_ = v_a_723_;
goto v___jp_708_;
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_a_700_);
lean_dec_ref(v___x_699_);
v_a_725_ = lean_ctor_get(v___y_714_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___y_714_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___y_714_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___y_714_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___boxed(lean_object* v_upperBound_860_, lean_object* v___x_861_, lean_object* v___x_862_, lean_object* v_a_863_, lean_object* v_b_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_upperBound_860_, v___x_861_, v___x_862_, v_a_863_, v_b_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___x_861_);
lean_dec(v_upperBound_860_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___x_889_; lean_object* v_mvarId_890_; lean_object* v_entries_891_; lean_object* v_ctx_892_; lean_object* v_simprocs_893_; lean_object* v_usedTheorems_894_; lean_object* v_diag_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_1002_; 
v___x_889_ = lean_st_ref_take(v_a_872_);
v_mvarId_890_ = lean_ctor_get(v___x_889_, 0);
v_entries_891_ = lean_ctor_get(v___x_889_, 1);
v_ctx_892_ = lean_ctor_get(v___x_889_, 2);
v_simprocs_893_ = lean_ctor_get(v___x_889_, 3);
v_usedTheorems_894_ = lean_ctor_get(v___x_889_, 4);
v_diag_895_ = lean_ctor_get(v___x_889_, 5);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_897_ = v___x_889_;
v_isShared_898_ = v_isSharedCheck_1002_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_diag_895_);
lean_inc(v_usedTheorems_894_);
lean_inc(v_simprocs_893_);
lean_inc(v_ctx_892_);
lean_inc(v_entries_891_);
lean_inc(v_mvarId_890_);
lean_dec(v___x_889_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_1002_;
goto v_resetjp_896_;
}
v___jp_878_:
{
lean_object* v___x_884_; uint8_t v_modified_885_; 
v___x_884_ = lean_st_ref_get(v___y_879_);
v_modified_885_ = lean_ctor_get_uint8(v___x_884_, sizeof(void*)*6);
lean_dec(v___x_884_);
if (v_modified_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_box(v_modified_885_);
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
else
{
v_a_872_ = v___y_879_;
v_a_873_ = v___y_880_;
v_a_874_ = v___y_881_;
v_a_875_ = v___y_882_;
v_a_876_ = v___y_883_;
goto _start;
}
}
v_resetjp_896_:
{
uint8_t v___x_899_; lean_object* v___x_901_; 
v___x_899_ = 0;
if (v_isShared_898_ == 0)
{
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_mvarId_890_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_entries_891_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_ctx_892_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_simprocs_893_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_usedTheorems_894_);
lean_ctor_set(v_reuseFailAlloc_1001_, 5, v_diag_895_);
v___x_901_ = v_reuseFailAlloc_1001_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v_simprocs_904_; lean_object* v___x_905_; lean_object* v_entries_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*6, v___x_899_);
v___x_902_ = lean_st_ref_put(v_a_872_, v___x_901_);
v___x_903_ = lean_st_ref_get(v_a_872_);
v_simprocs_904_ = lean_ctor_get(v___x_903_, 3);
lean_inc_ref_n(v_simprocs_904_, 2);
lean_dec(v___x_903_);
v___x_905_ = lean_st_ref_get(v_a_872_);
v_entries_906_ = lean_ctor_get(v___x_905_, 1);
lean_inc_ref(v_entries_906_);
lean_dec(v___x_905_);
v___x_907_ = lean_array_get_size(v_entries_906_);
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_box(0);
v___x_910_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0));
v___x_911_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v___x_907_, v_entries_906_, v_simprocs_904_, v___x_908_, v___x_910_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
lean_dec_ref(v_entries_906_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_992_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_992_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_992_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_992_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_fst_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_990_; 
v_fst_916_ = lean_ctor_get(v_a_912_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v_a_912_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v_a_912_, 1);
lean_dec(v_unused_991_);
v___x_918_ = v_a_912_;
v_isShared_919_ = v_isSharedCheck_990_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_fst_916_);
lean_dec(v_a_912_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_990_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
if (lean_obj_tag(v_fst_916_) == 0)
{
lean_object* v___x_920_; lean_object* v_mvarId_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_ctx_924_; lean_object* v_usedTheorems_925_; lean_object* v_diag_926_; uint8_t v___x_927_; lean_object* v___x_929_; 
lean_del_object(v___x_914_);
v___x_920_ = lean_st_ref_get(v_a_872_);
v_mvarId_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_mvarId_921_);
lean_dec(v___x_920_);
v___x_922_ = lean_st_ref_get(v_a_872_);
v___x_923_ = lean_st_ref_get(v_a_872_);
v_ctx_924_ = lean_ctor_get(v___x_922_, 2);
lean_inc_ref(v_ctx_924_);
lean_dec(v___x_922_);
v_usedTheorems_925_ = lean_ctor_get(v___x_923_, 4);
lean_inc_ref(v_usedTheorems_925_);
v_diag_926_ = lean_ctor_get(v___x_923_, 5);
lean_inc_ref(v_diag_926_);
lean_dec(v___x_923_);
v___x_927_ = 1;
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v_diag_926_);
lean_ctor_set(v___x_918_, 0, v_usedTheorems_925_);
v___x_929_ = v___x_918_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_usedTheorems_925_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_diag_926_);
v___x_929_ = v_reuseFailAlloc_985_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; 
lean_inc(v_mvarId_921_);
v___x_930_ = l_Lean_Meta_simpTarget(v_mvarId_921_, v_ctx_924_, v_simprocs_904_, v___x_909_, v___x_927_, v___x_929_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_976_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_976_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_976_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_976_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_fst_935_; lean_object* v_snd_936_; lean_object* v___x_937_; uint8_t v_modified_938_; lean_object* v_mvarId_939_; lean_object* v_entries_940_; lean_object* v_ctx_941_; lean_object* v_simprocs_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_973_; 
v_fst_935_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_fst_935_);
v_snd_936_ = lean_ctor_get(v_a_931_, 1);
lean_inc(v_snd_936_);
lean_dec(v_a_931_);
v___x_937_ = lean_st_ref_take(v_a_872_);
v_modified_938_ = lean_ctor_get_uint8(v___x_937_, sizeof(void*)*6);
v_mvarId_939_ = lean_ctor_get(v___x_937_, 0);
v_entries_940_ = lean_ctor_get(v___x_937_, 1);
v_ctx_941_ = lean_ctor_get(v___x_937_, 2);
v_simprocs_942_ = lean_ctor_get(v___x_937_, 3);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; lean_object* v_unused_975_; 
v_unused_974_ = lean_ctor_get(v___x_937_, 5);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v___x_937_, 4);
lean_dec(v_unused_975_);
v___x_944_ = v___x_937_;
v_isShared_945_ = v_isSharedCheck_973_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_simprocs_942_);
lean_inc(v_ctx_941_);
lean_inc(v_entries_940_);
lean_inc(v_mvarId_939_);
lean_dec(v___x_937_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_973_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_usedTheorems_946_; lean_object* v_diag_947_; lean_object* v___x_949_; 
v_usedTheorems_946_ = lean_ctor_get(v_snd_936_, 0);
lean_inc_ref(v_usedTheorems_946_);
v_diag_947_ = lean_ctor_get(v_snd_936_, 1);
lean_inc_ref(v_diag_947_);
lean_dec(v_snd_936_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 5, v_diag_947_);
lean_ctor_set(v___x_944_, 4, v_usedTheorems_946_);
v___x_949_ = v___x_944_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_mvarId_939_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_entries_940_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_ctx_941_);
lean_ctor_set(v_reuseFailAlloc_972_, 3, v_simprocs_942_);
lean_ctor_set(v_reuseFailAlloc_972_, 4, v_usedTheorems_946_);
lean_ctor_set(v_reuseFailAlloc_972_, 5, v_diag_947_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*6, v_modified_938_);
v___x_949_ = v_reuseFailAlloc_972_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; 
v___x_950_ = lean_st_ref_put(v_a_872_, v___x_949_);
if (lean_obj_tag(v_fst_935_) == 0)
{
lean_object* v___x_951_; lean_object* v___x_953_; 
lean_dec(v_mvarId_921_);
v___x_951_ = lean_box(v___x_927_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_951_);
v___x_953_ = v___x_933_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
else
{
lean_object* v_val_955_; uint8_t v___x_956_; 
lean_del_object(v___x_933_);
v_val_955_ = lean_ctor_get(v_fst_935_, 0);
lean_inc(v_val_955_);
lean_dec_ref_known(v_fst_935_, 1);
v___x_956_ = l_Lean_instBEqMVarId_beq(v_mvarId_921_, v_val_955_);
lean_dec(v_mvarId_921_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v_entries_958_; lean_object* v_ctx_959_; lean_object* v_simprocs_960_; lean_object* v_usedTheorems_961_; lean_object* v_diag_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_970_; 
v___x_957_ = lean_st_ref_take(v_a_872_);
v_entries_958_ = lean_ctor_get(v___x_957_, 1);
v_ctx_959_ = lean_ctor_get(v___x_957_, 2);
v_simprocs_960_ = lean_ctor_get(v___x_957_, 3);
v_usedTheorems_961_ = lean_ctor_get(v___x_957_, 4);
v_diag_962_ = lean_ctor_get(v___x_957_, 5);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; 
v_unused_971_ = lean_ctor_get(v___x_957_, 0);
lean_dec(v_unused_971_);
v___x_964_ = v___x_957_;
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_diag_962_);
lean_inc(v_usedTheorems_961_);
lean_inc(v_simprocs_960_);
lean_inc(v_ctx_959_);
lean_inc(v_entries_958_);
lean_dec(v___x_957_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v_val_955_);
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_val_955_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_entries_958_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_ctx_959_);
lean_ctor_set(v_reuseFailAlloc_969_, 3, v_simprocs_960_);
lean_ctor_set(v_reuseFailAlloc_969_, 4, v_usedTheorems_961_);
lean_ctor_set(v_reuseFailAlloc_969_, 5, v_diag_962_);
v___x_967_ = v_reuseFailAlloc_969_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_968_; 
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*6, v___x_927_);
v___x_968_ = lean_st_ref_put(v_a_872_, v___x_967_);
v___y_879_ = v_a_872_;
v___y_880_ = v_a_873_;
v___y_881_ = v_a_874_;
v___y_882_ = v_a_875_;
v___y_883_ = v_a_876_;
goto v___jp_878_;
}
}
}
else
{
lean_dec(v_val_955_);
v___y_879_ = v_a_872_;
v___y_880_ = v_a_873_;
v___y_881_ = v_a_874_;
v___y_882_ = v_a_875_;
v___y_883_ = v_a_876_;
goto v___jp_878_;
}
}
}
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_mvarId_921_);
v_a_977_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_930_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_930_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
else
{
lean_object* v_val_986_; lean_object* v___x_988_; 
lean_del_object(v___x_918_);
lean_dec_ref(v_simprocs_904_);
v_val_986_ = lean_ctor_get(v_fst_916_, 0);
lean_inc(v_val_986_);
lean_dec_ref_known(v_fst_916_, 1);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v_val_986_);
v___x_988_ = v___x_914_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_val_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec_ref(v_simprocs_904_);
v_a_993_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_911_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_911_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___boxed(lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(lean_object* v_cls_1010_, lean_object* v_msg_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_cls_1010_, v_msg_1011_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___boxed(lean_object* v_cls_1019_, lean_object* v_msg_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2(v_cls_1019_, v_msg_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(lean_object* v_upperBound_1028_, lean_object* v___x_1029_, lean_object* v___x_1030_, lean_object* v_inst_1031_, lean_object* v_R_1032_, lean_object* v_a_1033_, lean_object* v_b_1034_, lean_object* v_c_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_upperBound_1028_, v___x_1029_, v___x_1030_, v_a_1033_, v_b_1034_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___boxed(lean_object* v_upperBound_1043_, lean_object* v___x_1044_, lean_object* v___x_1045_, lean_object* v_inst_1046_, lean_object* v_R_1047_, lean_object* v_a_1048_, lean_object* v_b_1049_, lean_object* v_c_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3(v_upperBound_1043_, v___x_1044_, v___x_1045_, v_inst_1046_, v_R_1047_, v_a_1048_, v_b_1049_, v_c_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___x_1044_);
lean_dec(v_upperBound_1043_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(lean_object* v_as_1058_, size_t v_sz_1059_, size_t v_i_1060_, lean_object* v_b_1061_){
_start:
{
lean_object* v_a_1064_; uint8_t v___x_1068_; 
v___x_1068_ = lean_usize_dec_lt(v_i_1060_, v_sz_1059_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_b_1061_);
return v___x_1069_;
}
else
{
lean_object* v_snd_1070_; lean_object* v_fst_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1108_; 
v_snd_1070_ = lean_ctor_get(v_b_1061_, 1);
v_fst_1071_ = lean_ctor_get(v_b_1061_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_b_1061_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1073_ = v_b_1061_;
v_isShared_1074_ = v_isSharedCheck_1108_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_snd_1070_);
lean_inc(v_fst_1071_);
lean_dec(v_b_1061_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1108_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v_fst_1075_; lean_object* v_snd_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1107_; 
v_fst_1075_ = lean_ctor_get(v_snd_1070_, 0);
v_snd_1076_ = lean_ctor_get(v_snd_1070_, 1);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_snd_1070_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1078_ = v_snd_1070_;
v_isShared_1079_ = v_isSharedCheck_1107_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_snd_1076_);
lean_inc(v_fst_1075_);
lean_dec(v_snd_1070_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1107_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v_a_1080_; lean_object* v_fvarId_1081_; lean_object* v_userName_1082_; lean_object* v_origType_1083_; lean_object* v_type_1084_; lean_object* v_proof_1085_; uint8_t v___x_1099_; 
v_a_1080_ = lean_array_uget_borrowed(v_as_1058_, v_i_1060_);
v_fvarId_1081_ = lean_ctor_get(v_a_1080_, 0);
v_userName_1082_ = lean_ctor_get(v_a_1080_, 1);
v_origType_1083_ = lean_ctor_get(v_a_1080_, 3);
v_type_1084_ = lean_ctor_get(v_a_1080_, 4);
v_proof_1085_ = lean_ctor_get(v_a_1080_, 5);
lean_inc_ref(v_type_1084_);
v___x_1099_ = l_Lean_Expr_isTrue(v_type_1084_);
if (v___x_1099_ == 0)
{
uint8_t v___x_1100_; 
v___x_1100_ = lean_unbox(v_snd_1076_);
if (v___x_1100_ == 0)
{
uint8_t v___x_1101_; 
v___x_1101_ = lean_expr_eqv(v_type_1084_, v_origType_1083_);
if (v___x_1101_ == 0)
{
lean_dec(v_snd_1076_);
goto v___jp_1086_;
}
else
{
if (v___x_1099_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_del_object(v___x_1078_);
lean_del_object(v___x_1073_);
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v_fst_1075_);
lean_ctor_set(v___x_1102_, 1, v_snd_1076_);
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v_fst_1071_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v_a_1064_ = v___x_1103_;
goto v___jp_1063_;
}
else
{
lean_dec(v_snd_1076_);
goto v___jp_1086_;
}
}
}
else
{
lean_dec(v_snd_1076_);
goto v___jp_1086_;
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_del_object(v___x_1078_);
lean_del_object(v___x_1073_);
lean_inc(v_fvarId_1081_);
v___x_1104_ = lean_array_push(v_fst_1075_, v_fvarId_1081_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v_snd_1076_);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_fst_1071_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v_a_1064_ = v___x_1106_;
goto v___jp_1063_;
}
v___jp_1086_:
{
lean_object* v___x_1087_; uint8_t v___x_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
lean_inc(v_fvarId_1081_);
v___x_1087_ = lean_array_push(v_fst_1075_, v_fvarId_1081_);
v___x_1088_ = 0;
v___x_1089_ = 0;
lean_inc_ref(v_proof_1085_);
lean_inc_ref(v_type_1084_);
lean_inc(v_userName_1082_);
v___x_1090_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1090_, 0, v_userName_1082_);
lean_ctor_set(v___x_1090_, 1, v_type_1084_);
lean_ctor_set(v___x_1090_, 2, v_proof_1085_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*3, v___x_1088_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*3 + 1, v___x_1089_);
v___x_1091_ = lean_array_push(v_fst_1071_, v___x_1090_);
v___x_1092_ = lean_box(v___x_1068_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 1, v___x_1092_);
lean_ctor_set(v___x_1078_, 0, v___x_1087_);
v___x_1094_ = v___x_1078_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1096_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 1, v___x_1094_);
lean_ctor_set(v___x_1073_, 0, v___x_1091_);
v___x_1096_ = v___x_1073_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
v_a_1064_ = v___x_1096_;
goto v___jp_1063_;
}
}
}
}
}
}
v___jp_1063_:
{
size_t v___x_1065_; size_t v___x_1066_; 
v___x_1065_ = ((size_t)1ULL);
v___x_1066_ = lean_usize_add(v_i_1060_, v___x_1065_);
v_i_1060_ = v___x_1066_;
v_b_1061_ = v_a_1064_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg___boxed(lean_object* v_as_1109_, lean_object* v_sz_1110_, lean_object* v_i_1111_, lean_object* v_b_1112_, lean_object* v___y_1113_){
_start:
{
size_t v_sz_boxed_1114_; size_t v_i_boxed_1115_; lean_object* v_res_1116_; 
v_sz_boxed_1114_ = lean_unbox_usize(v_sz_1110_);
lean_dec(v_sz_1110_);
v_i_boxed_1115_ = lean_unbox_usize(v_i_1111_);
lean_dec(v_i_1111_);
v_res_1116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_as_1109_, v_sz_boxed_1114_, v_i_boxed_1115_, v_b_1112_);
lean_dec_ref(v_as_1109_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_main(lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v___x_1126_; 
lean_dec_ref_known(v___x_1125_, 1);
v___x_1126_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1187_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1187_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1187_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_unbox(v_a_1127_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v_mvarId_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v_entries_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; size_t v_sz_1139_; size_t v___x_1140_; lean_object* v___x_1141_; 
lean_del_object(v___x_1129_);
v___x_1132_ = lean_st_ref_get(v_a_1119_);
v_mvarId_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_mvarId_1133_);
lean_dec(v___x_1132_);
v___x_1134_ = ((lean_object*)(l_Lean_Meta_SimpAll_main___closed__0));
v___x_1135_ = lean_st_ref_get(v_a_1119_);
v_entries_1136_ = lean_ctor_get(v___x_1135_, 1);
lean_inc_ref(v_entries_1136_);
lean_dec(v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1134_);
lean_ctor_set(v___x_1137_, 1, v_a_1127_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1134_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v_sz_1139_ = lean_array_size(v_entries_1136_);
v___x_1140_ = ((size_t)0ULL);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_entries_1136_, v_sz_1139_, v___x_1140_, v___x_1138_);
lean_dec_ref(v_entries_1136_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v_snd_1143_; lean_object* v_fst_1144_; lean_object* v_fst_1145_; lean_object* v___x_1146_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v_snd_1143_ = lean_ctor_get(v_a_1142_, 1);
lean_inc(v_snd_1143_);
v_fst_1144_ = lean_ctor_get(v_a_1142_, 0);
lean_inc(v_fst_1144_);
lean_dec(v_a_1142_);
v_fst_1145_ = lean_ctor_get(v_snd_1143_, 0);
lean_inc(v_fst_1145_);
lean_dec(v_snd_1143_);
v___x_1146_ = l_Lean_MVarId_assertHypotheses(v_mvarId_1133_, v_fst_1144_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v_snd_1148_; lean_object* v___x_1149_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v_snd_1148_ = lean_ctor_get(v_a_1147_, 1);
lean_inc(v_snd_1148_);
lean_dec(v_a_1147_);
v___x_1149_ = l_Lean_MVarId_tryClearMany(v_snd_1148_, v_fst_1145_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
lean_dec(v_fst_1145_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1158_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_a_1150_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1154_);
v___x_1156_ = v___x_1152_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_a_1159_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1149_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1149_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_fst_1145_);
v_a_1167_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1146_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1146_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_mvarId_1133_);
v_a_1175_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1141_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1141_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_dec(v_a_1127_);
v___x_1183_ = lean_box(0);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1183_);
v___x_1185_ = v___x_1129_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
v_a_1188_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1126_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1126_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
v_a_1196_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1125_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1125_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_main___boxed(lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Meta_SimpAll_main(v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(lean_object* v_as_1211_, size_t v_sz_1212_, size_t v_i_1213_, lean_object* v_b_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_as_1211_, v_sz_1212_, v_i_1213_, v_b_1214_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___boxed(lean_object* v_as_1222_, lean_object* v_sz_1223_, lean_object* v_i_1224_, lean_object* v_b_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
size_t v_sz_boxed_1232_; size_t v_i_boxed_1233_; lean_object* v_res_1234_; 
v_sz_boxed_1232_ = lean_unbox_usize(v_sz_1223_);
lean_dec(v_sz_1223_);
v_i_boxed_1233_ = lean_unbox_usize(v_i_1224_);
lean_dec(v_i_1224_);
v_res_1234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0(v_as_1222_, v_sz_boxed_1232_, v_i_boxed_1233_, v_b_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v_as_1222_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(lean_object* v_mvarId_1235_, lean_object* v_x_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1235_, v_x_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
v_a_1251_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1242_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1242_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg___boxed(lean_object* v_mvarId_1259_, lean_object* v_x_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1259_, v_x_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(lean_object* v_00_u03b1_1267_, lean_object* v_mvarId_1268_, lean_object* v_x_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1268_, v_x_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___boxed(lean_object* v_00_u03b1_1276_, lean_object* v_mvarId_1277_, lean_object* v_x_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1(v_00_u03b1_1276_, v_mvarId_1277_, v_x_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(lean_object* v_msg_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_ref_1291_; lean_object* v___x_1292_; lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1301_; 
v_ref_1291_ = lean_ctor_get(v___y_1288_, 2);
v___x_1292_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msg_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1301_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
lean_inc(v_ref_1291_);
v___x_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1297_, 0, v_ref_1291_);
lean_ctor_set(v___x_1297_, 1, v_a_1293_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set_tag(v___x_1295_, 1);
lean_ctor_set(v___x_1295_, 0, v___x_1297_);
v___x_1299_ = v___x_1295_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg___boxed(lean_object* v_msg_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v_msg_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
return v_res_1308_;
}
}
static lean_object* _init_l_Lean_Meta_simpAll___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = ((lean_object*)(l_Lean_Meta_simpAll___lam__0___closed__0));
v___x_1311_ = l_Lean_stringToMessageData(v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___lam__0(lean_object* v___x_1312_, lean_object* v_ctx_1313_, lean_object* v_mvarId_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_st_mk_ref(v___x_1312_);
v___x_1321_ = l_Lean_Meta_SimpAll_main(v___x_1320_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1349_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1349_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1349_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_st_ref_get(v___x_1320_);
lean_dec(v___x_1320_);
if (lean_obj_tag(v_a_1322_) == 1)
{
lean_object* v_config_1335_; uint8_t v_failIfUnchanged_1336_; 
v_config_1335_ = lean_ctor_get(v_ctx_1313_, 0);
v_failIfUnchanged_1336_ = lean_ctor_get_uint8(v_config_1335_, sizeof(void*)*3 + 13);
if (v_failIfUnchanged_1336_ == 0)
{
goto v___jp_1327_;
}
else
{
lean_object* v_val_1337_; uint8_t v___x_1338_; 
v_val_1337_ = lean_ctor_get(v_a_1322_, 0);
v___x_1338_ = l_Lean_instBEqMVarId_beq(v_mvarId_1314_, v_val_1337_);
if (v___x_1338_ == 0)
{
goto v___jp_1327_;
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref_known(v_a_1322_, 1);
lean_dec(v___x_1326_);
lean_del_object(v___x_1324_);
v___x_1339_ = lean_obj_once(&l_Lean_Meta_simpAll___lam__0___closed__1, &l_Lean_Meta_simpAll___lam__0___closed__1_once, _init_l_Lean_Meta_simpAll___lam__0___closed__1);
v___x_1340_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v___x_1339_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
else
{
goto v___jp_1327_;
}
v___jp_1327_:
{
lean_object* v_usedTheorems_1328_; lean_object* v_diag_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v_usedTheorems_1328_ = lean_ctor_get(v___x_1326_, 4);
lean_inc_ref(v_usedTheorems_1328_);
v_diag_1329_ = lean_ctor_get(v___x_1326_, 5);
lean_inc_ref(v_diag_1329_);
lean_dec(v___x_1326_);
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_usedTheorems_1328_);
lean_ctor_set(v___x_1330_, 1, v_diag_1329_);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_a_1322_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1331_);
v___x_1333_ = v___x_1324_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v___x_1320_);
v_a_1350_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1321_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1321_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___lam__0___boxed(lean_object* v___x_1358_, lean_object* v_ctx_1359_, lean_object* v_mvarId_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Meta_simpAll___lam__0(v___x_1358_, v_ctx_1359_, v_mvarId_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v_mvarId_1360_);
lean_dec_ref(v_ctx_1359_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll(lean_object* v_mvarId_1369_, lean_object* v_ctx_1370_, lean_object* v_simprocs_1371_, lean_object* v_stats_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_usedTheorems_1378_; lean_object* v_diag_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___f_1383_; lean_object* v___x_1384_; 
v_usedTheorems_1378_ = lean_ctor_get(v_stats_1372_, 0);
v_diag_1379_ = lean_ctor_get(v_stats_1372_, 1);
v___x_1380_ = 0;
v___x_1381_ = ((lean_object*)(l_Lean_Meta_simpAll___closed__0));
lean_inc_ref(v_diag_1379_);
lean_inc_ref(v_usedTheorems_1378_);
lean_inc_ref(v_ctx_1370_);
lean_inc_n(v_mvarId_1369_, 2);
v___x_1382_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1382_, 0, v_mvarId_1369_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
lean_ctor_set(v___x_1382_, 2, v_ctx_1370_);
lean_ctor_set(v___x_1382_, 3, v_simprocs_1371_);
lean_ctor_set(v___x_1382_, 4, v_usedTheorems_1378_);
lean_ctor_set(v___x_1382_, 5, v_diag_1379_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*6, v___x_1380_);
v___f_1383_ = lean_alloc_closure((void*)(l_Lean_Meta_simpAll___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1383_, 0, v___x_1382_);
lean_closure_set(v___f_1383_, 1, v_ctx_1370_);
lean_closure_set(v___f_1383_, 2, v_mvarId_1369_);
v___x_1384_ = l_Lean_MVarId_withContext___at___00Lean_Meta_simpAll_spec__1___redArg(v_mvarId_1369_, v___f_1383_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___boxed(lean_object* v_mvarId_1385_, lean_object* v_ctx_1386_, lean_object* v_simprocs_1387_, lean_object* v_stats_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Meta_simpAll(v_mvarId_1385_, v_ctx_1386_, v_simprocs_1387_, v_stats_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec_ref(v_stats_1388_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(lean_object* v_00_u03b1_1395_, lean_object* v_msg_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___redArg(v_msg_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0___boxed(lean_object* v_00_u03b1_1403_, lean_object* v_msg_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_throwError___at___00Lean_Meta_simpAll_spec__0(v_00_u03b1_1403_, v_msg_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1480_; uint8_t v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1480_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_1481_ = 0;
v___x_1482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_));
v___x_1483_ = l_Lean_registerTraceClass(v___x_1480_, v___x_1481_, v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2____boxed(lean_object* v_a_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Simp_SimpAll_816399212____hygCtx___hyg_2_();
return v_res_1485_;
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
