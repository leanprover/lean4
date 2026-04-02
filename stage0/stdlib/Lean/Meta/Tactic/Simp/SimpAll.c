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
lean_inc(v_a_185_);
v___x_188_ = l_Lean_FVarId_getDecl___redArg(v_a_185_, v___y_173_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_190_; lean_object* v_ctx_191_; lean_object* v_indexConfig_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc_n(v_a_189_, 2);
lean_dec_ref(v___x_188_);
v___x_190_ = lean_st_ref_get(v___y_172_);
v_ctx_191_ = lean_ctor_get(v___x_190_, 2);
lean_inc_ref(v_ctx_191_);
lean_dec(v___x_190_);
v_indexConfig_192_ = lean_ctor_get(v_ctx_191_, 4);
lean_inc_ref(v_indexConfig_192_);
lean_dec_ref(v_ctx_191_);
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
lean_inc_n(v_a_214_, 2);
lean_dec_ref(v___x_213_);
v___x_215_ = l_Lean_LocalDecl_userName(v_a_189_);
lean_dec(v_a_189_);
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
lean_dec_ref(v_x_415_);
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
lean_dec_ref(v_x_415_);
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
lean_object* v___x_479_; lean_object* v_env_480_; lean_object* v___x_481_; lean_object* v_mctx_482_; lean_object* v_lctx_483_; lean_object* v_options_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_479_ = lean_st_ref_get(v___y_477_);
v_env_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc_ref(v_env_480_);
lean_dec(v___x_479_);
v___x_481_ = lean_st_ref_get(v___y_475_);
v_mctx_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc_ref(v_mctx_482_);
lean_dec(v___x_481_);
v_lctx_483_ = lean_ctor_get(v___y_474_, 2);
v_options_484_ = lean_ctor_get(v___y_476_, 2);
lean_inc_ref(v_options_484_);
lean_inc_ref(v_lctx_483_);
v___x_485_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_485_, 0, v_env_480_);
lean_ctor_set(v___x_485_, 1, v_mctx_482_);
lean_ctor_set(v___x_485_, 2, v_lctx_483_);
lean_ctor_set(v___x_485_, 3, v_options_484_);
v___x_486_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v_msgData_473_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2___boxed(lean_object* v_msgData_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msgData_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
return v_res_494_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_495_; double v___x_496_; 
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_float_of_nat(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(lean_object* v_cls_500_, lean_object* v_msg_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_ref_507_; lean_object* v___x_508_; lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_553_; 
v_ref_507_ = lean_ctor_get(v___y_504_, 5);
v___x_508_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2_spec__2(v_msg_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_553_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_553_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_553_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v_traceState_514_; lean_object* v_env_515_; lean_object* v_nextMacroScope_516_; lean_object* v_ngen_517_; lean_object* v_auxDeclNGen_518_; lean_object* v_cache_519_; lean_object* v_messages_520_; lean_object* v_infoState_521_; lean_object* v_snapshotTasks_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_552_; 
v___x_513_ = lean_st_ref_take(v___y_505_);
v_traceState_514_ = lean_ctor_get(v___x_513_, 4);
v_env_515_ = lean_ctor_get(v___x_513_, 0);
v_nextMacroScope_516_ = lean_ctor_get(v___x_513_, 1);
v_ngen_517_ = lean_ctor_get(v___x_513_, 2);
v_auxDeclNGen_518_ = lean_ctor_get(v___x_513_, 3);
v_cache_519_ = lean_ctor_get(v___x_513_, 5);
v_messages_520_ = lean_ctor_get(v___x_513_, 6);
v_infoState_521_ = lean_ctor_get(v___x_513_, 7);
v_snapshotTasks_522_ = lean_ctor_get(v___x_513_, 8);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_552_ == 0)
{
v___x_524_ = v___x_513_;
v_isShared_525_ = v_isSharedCheck_552_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_snapshotTasks_522_);
lean_inc(v_infoState_521_);
lean_inc(v_messages_520_);
lean_inc(v_cache_519_);
lean_inc(v_traceState_514_);
lean_inc(v_auxDeclNGen_518_);
lean_inc(v_ngen_517_);
lean_inc(v_nextMacroScope_516_);
lean_inc(v_env_515_);
lean_dec(v___x_513_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_552_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
uint64_t v_tid_526_; lean_object* v_traces_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_551_; 
v_tid_526_ = lean_ctor_get_uint64(v_traceState_514_, sizeof(void*)*1);
v_traces_527_ = lean_ctor_get(v_traceState_514_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v_traceState_514_);
if (v_isSharedCheck_551_ == 0)
{
v___x_529_ = v_traceState_514_;
v_isShared_530_ = v_isSharedCheck_551_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_traces_527_);
lean_dec(v_traceState_514_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_551_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; double v___x_532_; uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_531_ = lean_box(0);
v___x_532_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__0);
v___x_533_ = 0;
v___x_534_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__1));
v___x_535_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_535_, 0, v_cls_500_);
lean_ctor_set(v___x_535_, 1, v___x_531_);
lean_ctor_set(v___x_535_, 2, v___x_534_);
lean_ctor_set_float(v___x_535_, sizeof(void*)*3, v___x_532_);
lean_ctor_set_float(v___x_535_, sizeof(void*)*3 + 8, v___x_532_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*3 + 16, v___x_533_);
v___x_536_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___closed__2));
v___x_537_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v_a_509_);
lean_ctor_set(v___x_537_, 2, v___x_536_);
lean_inc(v_ref_507_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v_ref_507_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = l_Lean_PersistentArray_push___redArg(v_traces_527_, v___x_538_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_539_);
v___x_541_ = v___x_529_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_539_);
lean_ctor_set_uint64(v_reuseFailAlloc_550_, sizeof(void*)*1, v_tid_526_);
v___x_541_ = v_reuseFailAlloc_550_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 4, v___x_541_);
v___x_543_ = v___x_524_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_env_515_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_nextMacroScope_516_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v_ngen_517_);
lean_ctor_set(v_reuseFailAlloc_549_, 3, v_auxDeclNGen_518_);
lean_ctor_set(v_reuseFailAlloc_549_, 4, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_549_, 5, v_cache_519_);
lean_ctor_set(v_reuseFailAlloc_549_, 6, v_messages_520_);
lean_ctor_set(v_reuseFailAlloc_549_, 7, v_infoState_521_);
lean_ctor_set(v_reuseFailAlloc_549_, 8, v_snapshotTasks_522_);
v___x_543_ = v_reuseFailAlloc_549_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_544_ = lean_st_ref_set(v___y_505_, v___x_543_);
v___x_545_ = lean_box(0);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_545_);
v___x_547_ = v___x_511_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg___boxed(lean_object* v_cls_554_, lean_object* v_msg_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v_cls_554_, v_msg_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(lean_object* v_fst_562_, lean_object* v_snd_563_, lean_object* v___x_564_, lean_object* v_fvarId_565_, uint8_t v___x_566_, lean_object* v___x_567_, lean_object* v_a_568_, lean_object* v___x_569_, lean_object* v_userName_570_, lean_object* v_origType_571_, lean_object* v_____r_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_st_ref_get(v___y_573_);
v___x_580_ = l_Lean_mkFreshId___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__0___redArg(v___y_577_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref(v___x_580_);
lean_inc_ref(v_snd_563_);
lean_inc_ref(v_fst_562_);
v___x_582_ = l_Lean_Meta_mkExpectedTypeHint(v_fst_562_, v_snd_563_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_ctx_583_; lean_object* v_a_584_; lean_object* v_simpTheorems_585_; lean_object* v_indexConfig_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_ctx_583_ = lean_ctor_get(v___x_579_, 2);
lean_inc_ref(v_ctx_583_);
lean_dec(v___x_579_);
v_a_584_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_584_);
lean_dec_ref(v___x_582_);
v_simpTheorems_585_ = lean_ctor_get(v_ctx_583_, 5);
lean_inc_ref(v_simpTheorems_585_);
lean_dec_ref(v_ctx_583_);
v_indexConfig_586_ = lean_ctor_get(v___x_564_, 4);
lean_inc(v_fvarId_565_);
v___x_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_587_, 0, v_fvarId_565_);
v___x_588_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(v_simpTheorems_585_, v___x_587_);
v___x_589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_589_, 0, v_a_581_);
lean_inc_ref(v_indexConfig_586_);
lean_inc_ref(v___x_589_);
v___x_590_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v___x_588_, v___x_589_, v_a_584_, v_indexConfig_586_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_622_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_622_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_622_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_622_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v_mvarId_596_; lean_object* v_entries_597_; lean_object* v_simprocs_598_; lean_object* v_usedTheorems_599_; lean_object* v_diag_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_620_; 
v___x_595_ = lean_st_ref_take(v___y_573_);
v_mvarId_596_ = lean_ctor_get(v___x_595_, 0);
v_entries_597_ = lean_ctor_get(v___x_595_, 1);
v_simprocs_598_ = lean_ctor_get(v___x_595_, 3);
v_usedTheorems_599_ = lean_ctor_get(v___x_595_, 4);
v_diag_600_ = lean_ctor_get(v___x_595_, 5);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v___x_595_, 2);
lean_dec(v_unused_621_);
v___x_602_ = v___x_595_;
v_isShared_603_ = v_isSharedCheck_620_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_diag_600_);
lean_inc(v_usedTheorems_599_);
lean_inc(v_simprocs_598_);
lean_inc(v_entries_597_);
lean_inc(v_mvarId_596_);
lean_dec(v___x_595_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_620_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___y_605_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_array_get_size(v_entries_597_);
v___x_616_ = lean_nat_dec_lt(v_a_568_, v___x_615_);
if (v___x_616_ == 0)
{
lean_dec_ref(v___x_589_);
lean_dec_ref(v_origType_571_);
lean_dec(v_userName_570_);
lean_dec(v_fvarId_565_);
lean_dec_ref(v_snd_563_);
lean_dec_ref(v_fst_562_);
v___y_605_ = v_entries_597_;
goto v___jp_604_;
}
else
{
lean_object* v_xs_x27_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_xs_x27_617_ = lean_array_fset(v_entries_597_, v_a_568_, v___x_569_);
v___x_618_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_618_, 0, v_fvarId_565_);
lean_ctor_set(v___x_618_, 1, v_userName_570_);
lean_ctor_set(v___x_618_, 2, v___x_589_);
lean_ctor_set(v___x_618_, 3, v_origType_571_);
lean_ctor_set(v___x_618_, 4, v_snd_563_);
lean_ctor_set(v___x_618_, 5, v_fst_562_);
v___x_619_ = lean_array_fset(v_xs_x27_617_, v_a_568_, v___x_618_);
v___y_605_ = v___x_619_;
goto v___jp_604_;
}
v___jp_604_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v___x_564_, v_a_591_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 2, v___x_606_);
lean_ctor_set(v___x_602_, 1, v___y_605_);
v___x_608_ = v___x_602_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_mvarId_596_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___y_605_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_simprocs_598_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v_usedTheorems_599_);
lean_ctor_set(v_reuseFailAlloc_614_, 5, v_diag_600_);
v___x_608_ = v_reuseFailAlloc_614_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*6, v___x_566_);
v___x_609_ = lean_st_ref_set(v___y_573_, v___x_608_);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_567_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_610_);
v___x_612_ = v___x_593_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v___x_589_);
lean_dec_ref(v_origType_571_);
lean_dec(v_userName_570_);
lean_dec_ref(v___x_567_);
lean_dec(v_fvarId_565_);
lean_dec_ref(v___x_564_);
lean_dec_ref(v_snd_563_);
lean_dec_ref(v_fst_562_);
v_a_623_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_590_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_590_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_a_581_);
lean_dec(v___x_579_);
lean_dec_ref(v_origType_571_);
lean_dec(v_userName_570_);
lean_dec_ref(v___x_567_);
lean_dec(v_fvarId_565_);
lean_dec_ref(v___x_564_);
lean_dec_ref(v_snd_563_);
lean_dec_ref(v_fst_562_);
v_a_631_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_582_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_582_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v___x_579_);
lean_dec_ref(v_origType_571_);
lean_dec(v_userName_570_);
lean_dec_ref(v___x_567_);
lean_dec(v_fvarId_565_);
lean_dec_ref(v___x_564_);
lean_dec_ref(v_snd_563_);
lean_dec_ref(v_fst_562_);
v_a_639_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_580_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_580_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_fst_647_ = _args[0];
lean_object* v_snd_648_ = _args[1];
lean_object* v___x_649_ = _args[2];
lean_object* v_fvarId_650_ = _args[3];
lean_object* v___x_651_ = _args[4];
lean_object* v___x_652_ = _args[5];
lean_object* v_a_653_ = _args[6];
lean_object* v___x_654_ = _args[7];
lean_object* v_userName_655_ = _args[8];
lean_object* v_origType_656_ = _args[9];
lean_object* v_____r_657_ = _args[10];
lean_object* v___y_658_ = _args[11];
lean_object* v___y_659_ = _args[12];
lean_object* v___y_660_ = _args[13];
lean_object* v___y_661_ = _args[14];
lean_object* v___y_662_ = _args[15];
lean_object* v___y_663_ = _args[16];
_start:
{
uint8_t v___x_27748__boxed_664_; lean_object* v_res_665_; 
v___x_27748__boxed_664_ = lean_unbox(v___x_651_);
v_res_665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fst_647_, v_snd_648_, v___x_649_, v_fvarId_650_, v___x_27748__boxed_664_, v___x_652_, v_a_653_, v___x_654_, v_userName_655_, v_origType_656_, v_____r_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec(v_a_653_);
return v_res_665_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_682_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__7));
v___x_683_ = l_Lean_Name_append(v___x_682_, v___x_681_);
return v___x_683_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__9));
v___x_686_ = l_Lean_stringToMessageData(v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__11));
v___x_689_ = l_Lean_stringToMessageData(v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__13));
v___x_692_ = l_Lean_stringToMessageData(v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(lean_object* v_upperBound_693_, lean_object* v___x_694_, lean_object* v___x_695_, lean_object* v_a_696_, lean_object* v_b_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_a_705_; lean_object* v___y_710_; uint8_t v___x_729_; 
v___x_729_ = lean_nat_dec_lt(v_a_696_, v_upperBound_693_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
lean_dec(v_a_696_);
lean_dec_ref(v___x_695_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v_b_697_);
return v___x_730_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_ctx_735_; lean_object* v_ctx_736_; lean_object* v_simpTheorems_737_; lean_object* v___x_738_; lean_object* v_fvarId_739_; lean_object* v_userName_740_; lean_object* v_id_741_; lean_object* v_origType_742_; lean_object* v_type_743_; lean_object* v_proof_744_; lean_object* v_mvarId_745_; lean_object* v_usedTheorems_746_; lean_object* v_diag_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec_ref(v_b_697_);
v___x_731_ = lean_st_ref_get(v___y_698_);
v___x_732_ = lean_st_ref_get(v___y_698_);
v___x_733_ = lean_st_ref_get(v___y_698_);
v___x_734_ = lean_st_ref_get(v___y_698_);
v_ctx_735_ = lean_ctor_get(v___x_732_, 2);
lean_inc_ref(v_ctx_735_);
lean_dec(v___x_732_);
v_ctx_736_ = lean_ctor_get(v___x_731_, 2);
lean_inc_ref(v_ctx_736_);
lean_dec(v___x_731_);
v_simpTheorems_737_ = lean_ctor_get(v_ctx_735_, 5);
lean_inc_ref(v_simpTheorems_737_);
lean_dec_ref(v_ctx_735_);
v___x_738_ = lean_array_fget_borrowed(v___x_694_, v_a_696_);
v_fvarId_739_ = lean_ctor_get(v___x_738_, 0);
v_userName_740_ = lean_ctor_get(v___x_738_, 1);
v_id_741_ = lean_ctor_get(v___x_738_, 2);
v_origType_742_ = lean_ctor_get(v___x_738_, 3);
v_type_743_ = lean_ctor_get(v___x_738_, 4);
v_proof_744_ = lean_ctor_get(v___x_738_, 5);
v_mvarId_745_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_mvarId_745_);
lean_dec(v___x_733_);
v_usedTheorems_746_ = lean_ctor_get(v___x_734_, 4);
lean_inc_ref(v_usedTheorems_746_);
v_diag_747_ = lean_ctor_get(v___x_734_, 5);
lean_inc_ref(v_diag_747_);
lean_dec(v___x_734_);
lean_inc_ref(v_id_741_);
v___x_748_ = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(v_simpTheorems_737_, v_id_741_);
v___x_749_ = l_Lean_Meta_Simp_Context_setSimpTheorems(v_ctx_736_, v___x_748_);
v___x_750_ = lean_box(0);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_usedTheorems_746_);
lean_ctor_set(v___x_751_, 1, v_diag_747_);
lean_inc_ref(v___x_695_);
lean_inc_ref(v___x_749_);
lean_inc_ref(v_type_743_);
lean_inc_ref(v_proof_744_);
v___x_752_ = l_Lean_Meta_simpStep(v_mvarId_745_, v_proof_744_, v_type_743_, v___x_749_, v___x_695_, v___x_750_, v___x_729_, v___x_751_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec_ref(v___x_751_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_846_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_846_ == 0)
{
v___x_755_ = v___x_752_;
v_isShared_756_ = v_isSharedCheck_846_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_846_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_fst_757_; lean_object* v_snd_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_845_; 
v_fst_757_ = lean_ctor_get(v_a_753_, 0);
v_snd_758_ = lean_ctor_get(v_a_753_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_a_753_);
if (v_isSharedCheck_845_ == 0)
{
v___x_760_ = v_a_753_;
v_isShared_761_ = v_isSharedCheck_845_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_snd_758_);
lean_inc(v_fst_757_);
lean_dec(v_a_753_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_845_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; uint8_t v_modified_763_; lean_object* v_mvarId_764_; lean_object* v_entries_765_; lean_object* v_ctx_766_; lean_object* v_simprocs_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_842_; 
v___x_762_ = lean_st_ref_take(v___y_698_);
v_modified_763_ = lean_ctor_get_uint8(v___x_762_, sizeof(void*)*6);
v_mvarId_764_ = lean_ctor_get(v___x_762_, 0);
v_entries_765_ = lean_ctor_get(v___x_762_, 1);
v_ctx_766_ = lean_ctor_get(v___x_762_, 2);
v_simprocs_767_ = lean_ctor_get(v___x_762_, 3);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; lean_object* v_unused_844_; 
v_unused_843_ = lean_ctor_get(v___x_762_, 5);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v___x_762_, 4);
lean_dec(v_unused_844_);
v___x_769_ = v___x_762_;
v_isShared_770_ = v_isSharedCheck_842_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_simprocs_767_);
lean_inc(v_ctx_766_);
lean_inc(v_entries_765_);
lean_inc(v_mvarId_764_);
lean_dec(v___x_762_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_842_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_usedTheorems_771_; lean_object* v_diag_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_841_; 
v_usedTheorems_771_ = lean_ctor_get(v_snd_758_, 0);
v_diag_772_ = lean_ctor_get(v_snd_758_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_snd_758_);
if (v_isSharedCheck_841_ == 0)
{
v___x_774_ = v_snd_758_;
v_isShared_775_ = v_isSharedCheck_841_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_diag_772_);
lean_inc(v_usedTheorems_771_);
lean_dec(v_snd_758_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_841_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 5, v_diag_772_);
lean_ctor_set(v___x_769_, 4, v_usedTheorems_771_);
v___x_777_ = v___x_769_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_mvarId_764_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_entries_765_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_ctx_766_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_simprocs_767_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v_usedTheorems_771_);
lean_ctor_set(v_reuseFailAlloc_840_, 5, v_diag_772_);
lean_ctor_set_uint8(v_reuseFailAlloc_840_, sizeof(void*)*6, v_modified_763_);
v___x_777_ = v_reuseFailAlloc_840_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_st_ref_set(v___y_698_, v___x_777_);
v___x_779_ = lean_box(0);
if (lean_obj_tag(v_fst_757_) == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
lean_del_object(v___x_774_);
lean_dec_ref(v___x_749_);
lean_dec(v_a_696_);
lean_dec_ref(v___x_695_);
v___x_780_ = lean_box(v___x_729_);
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v___x_779_);
lean_ctor_set(v___x_760_, 0, v___x_781_);
v___x_783_ = v___x_760_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v___x_779_);
v___x_783_ = v_reuseFailAlloc_787_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_785_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_783_);
v___x_785_ = v___x_755_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
lean_object* v_val_788_; lean_object* v_fst_789_; lean_object* v_snd_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_839_; 
lean_del_object(v___x_760_);
lean_del_object(v___x_755_);
v_val_788_ = lean_ctor_get(v_fst_757_, 0);
lean_inc(v_val_788_);
lean_dec_ref(v_fst_757_);
v_fst_789_ = lean_ctor_get(v_val_788_, 0);
v_snd_790_ = lean_ctor_get(v_val_788_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_val_788_);
if (v_isSharedCheck_839_ == 0)
{
v___x_792_ = v_val_788_;
v_isShared_793_ = v_isSharedCheck_839_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_snd_790_);
lean_inc(v_fst_789_);
lean_dec(v_val_788_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_839_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__0));
v___x_795_ = lean_expr_eqv(v_snd_790_, v_type_743_);
if (v___x_795_ == 0)
{
lean_object* v_options_796_; lean_object* v_inheritedTraceOptions_797_; uint8_t v_hasTrace_798_; 
v_options_796_ = lean_ctor_get(v___y_701_, 2);
v_inheritedTraceOptions_797_ = lean_ctor_get(v___y_701_, 13);
v_hasTrace_798_ = lean_ctor_get_uint8(v_options_796_, sizeof(void*)*1);
if (v_hasTrace_798_ == 0)
{
lean_del_object(v___x_792_);
lean_del_object(v___x_774_);
goto v___jp_799_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_801_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__5));
v___x_802_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__8);
v___x_803_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_797_, v_options_796_, v___x_802_);
if (v___x_803_ == 0)
{
lean_del_object(v___x_792_);
lean_del_object(v___x_774_);
goto v___jp_799_;
}
else
{
lean_object* v___x_804_; 
lean_inc_ref(v_id_741_);
v___x_804_ = l_Lean_Meta_ppOrigin___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__1___redArg(v_id_741_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref(v___x_804_);
v___x_806_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__10);
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 7);
lean_ctor_set(v___x_792_, 1, v_a_805_);
lean_ctor_set(v___x_792_, 0, v___x_806_);
v___x_808_ = v___x_792_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_a_805_);
v___x_808_ = v_reuseFailAlloc_830_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__12);
if (v_isShared_775_ == 0)
{
lean_ctor_set_tag(v___x_774_, 7);
lean_ctor_set(v___x_774_, 1, v___x_809_);
lean_ctor_set(v___x_774_, 0, v___x_808_);
v___x_811_ = v___x_774_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_809_);
v___x_811_ = v_reuseFailAlloc_829_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
lean_inc_ref(v_type_743_);
v___x_812_ = l_Lean_MessageData_ofExpr(v_type_743_);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___closed__14);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
lean_inc(v_snd_790_);
v___x_816_ = l_Lean_MessageData_ofExpr(v_snd_790_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__2___redArg(v___x_801_, v___x_817_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref(v___x_818_);
lean_inc_ref(v_origType_742_);
lean_inc(v_userName_740_);
lean_inc(v_fvarId_739_);
v___x_820_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fst_789_, v_snd_790_, v___x_749_, v_fvarId_739_, v___x_729_, v___x_794_, v_a_696_, v___x_779_, v_userName_740_, v_origType_742_, v_a_819_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
v___y_710_ = v___x_820_;
goto v___jp_709_;
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_snd_790_);
lean_dec(v_fst_789_);
lean_dec_ref(v___x_749_);
lean_dec(v_a_696_);
lean_dec_ref(v___x_695_);
v_a_821_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_818_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_818_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_del_object(v___x_792_);
lean_dec(v_snd_790_);
lean_dec(v_fst_789_);
lean_del_object(v___x_774_);
lean_dec_ref(v___x_749_);
lean_dec(v_a_696_);
lean_dec_ref(v___x_695_);
v_a_831_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_804_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_804_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
v___jp_799_:
{
lean_object* v___x_800_; 
lean_inc_ref(v_origType_742_);
lean_inc(v_userName_740_);
lean_inc(v_fvarId_739_);
v___x_800_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___lam__0(v_fst_789_, v_snd_790_, v___x_749_, v_fvarId_739_, v___x_729_, v___x_794_, v_a_696_, v___x_779_, v_userName_740_, v_origType_742_, v___x_779_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
v___y_710_ = v___x_800_;
goto v___jp_709_;
}
}
else
{
lean_del_object(v___x_792_);
lean_dec(v_snd_790_);
lean_dec(v_fst_789_);
lean_del_object(v___x_774_);
lean_dec_ref(v___x_749_);
v_a_705_ = v___x_794_;
goto v___jp_704_;
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
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec_ref(v___x_749_);
lean_dec(v_a_696_);
lean_dec_ref(v___x_695_);
v_a_847_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_752_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_752_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
v___jp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = lean_nat_add(v_a_696_, v___x_706_);
lean_dec(v_a_696_);
v_a_696_ = v___x_707_;
v_b_697_ = v_a_705_;
goto _start;
}
v___jp_709_:
{
if (lean_obj_tag(v___y_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_720_; 
v_a_711_ = lean_ctor_get(v___y_710_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___y_710_);
if (v_isSharedCheck_720_ == 0)
{
v___x_713_ = v___y_710_;
v_isShared_714_ = v_isSharedCheck_720_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___y_710_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_720_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
if (lean_obj_tag(v_a_711_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; 
lean_dec(v_a_696_);
lean_dec_ref(v___x_695_);
v_a_715_ = lean_ctor_get(v_a_711_, 0);
lean_inc(v_a_715_);
lean_dec_ref(v_a_711_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v_a_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
else
{
lean_object* v_a_719_; 
lean_del_object(v___x_713_);
v_a_719_ = lean_ctor_get(v_a_711_, 0);
lean_inc(v_a_719_);
lean_dec_ref(v_a_711_);
v_a_705_ = v_a_719_;
goto v___jp_704_;
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec(v_a_696_);
lean_dec_ref(v___x_695_);
v_a_721_ = lean_ctor_get(v___y_710_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___y_710_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___y_710_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___y_710_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg___boxed(lean_object* v_upperBound_855_, lean_object* v___x_856_, lean_object* v___x_857_, lean_object* v_a_858_, lean_object* v_b_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v_upperBound_855_, v___x_856_, v___x_857_, v_a_858_, v_b_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___x_856_);
lean_dec(v_upperBound_855_);
return v_res_866_;
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
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v_entries_903_; lean_object* v_simprocs_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
lean_ctor_set_uint8(v___x_899_, sizeof(void*)*6, v___x_897_);
v___x_900_ = lean_st_ref_set(v_a_870_, v___x_899_);
v___x_901_ = lean_st_ref_get(v_a_870_);
v___x_902_ = lean_st_ref_get(v_a_870_);
v_entries_903_ = lean_ctor_get(v___x_902_, 1);
lean_inc_ref(v_entries_903_);
lean_dec(v___x_902_);
v_simprocs_904_ = lean_ctor_get(v___x_901_, 3);
lean_inc_ref_n(v_simprocs_904_, 2);
lean_dec(v___x_901_);
v___x_905_ = lean_array_get_size(v_entries_903_);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_box(0);
v___x_908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__0));
v___x_909_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_spec__3___redArg(v___x_905_, v_entries_903_, v_simprocs_904_, v___x_906_, v___x_908_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
lean_dec_ref(v_entries_903_);
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
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v_mvarId_921_; lean_object* v_ctx_922_; lean_object* v_usedTheorems_923_; lean_object* v_diag_924_; uint8_t v___x_925_; lean_object* v___x_927_; 
lean_del_object(v___x_912_);
v___x_918_ = lean_st_ref_get(v_a_870_);
v___x_919_ = lean_st_ref_get(v_a_870_);
v___x_920_ = lean_st_ref_get(v_a_870_);
v_mvarId_921_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_mvarId_921_);
lean_dec(v___x_918_);
v_ctx_922_ = lean_ctor_get(v___x_919_, 2);
lean_inc_ref(v_ctx_922_);
lean_dec(v___x_919_);
v_usedTheorems_923_ = lean_ctor_get(v___x_920_, 4);
lean_inc_ref(v_usedTheorems_923_);
v_diag_924_ = lean_ctor_get(v___x_920_, 5);
lean_inc_ref(v_diag_924_);
lean_dec(v___x_920_);
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
lean_inc(v_mvarId_921_);
v___x_928_ = l_Lean_Meta_simpTarget(v_mvarId_921_, v_ctx_922_, v_simprocs_904_, v___x_907_, v___x_925_, v___x_927_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
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
v___x_948_ = lean_st_ref_set(v_a_870_, v___x_947_);
if (lean_obj_tag(v_fst_933_) == 0)
{
lean_object* v___x_949_; lean_object* v___x_951_; 
lean_dec(v_mvarId_921_);
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
lean_dec_ref(v_fst_933_);
v___x_954_ = l_Lean_instBEqMVarId_beq(v_mvarId_921_, v_val_953_);
lean_dec(v_mvarId_921_);
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
v___x_966_ = lean_st_ref_set(v_a_870_, v___x_965_);
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
lean_dec(v_mvarId_921_);
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
lean_dec_ref(v_simprocs_904_);
v_val_984_ = lean_ctor_get(v_fst_914_, 0);
lean_inc(v_val_984_);
lean_dec_ref(v_fst_914_);
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
lean_dec_ref(v_simprocs_904_);
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
lean_dec_ref(v___x_1123_);
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
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v_entries_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; size_t v_sz_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
lean_del_object(v___x_1127_);
v___x_1130_ = lean_st_ref_get(v_a_1117_);
v___x_1131_ = lean_st_ref_get(v_a_1117_);
v_entries_1132_ = lean_ctor_get(v___x_1131_, 1);
lean_inc_ref(v_entries_1132_);
lean_dec(v___x_1131_);
v___x_1133_ = ((lean_object*)(l_Lean_Meta_SimpAll_main___closed__0));
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v_a_1125_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v_sz_1136_ = lean_array_size(v_entries_1132_);
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_SimpAll_main_spec__0___redArg(v_entries_1132_, v_sz_1136_, v___x_1137_, v___x_1135_);
lean_dec_ref(v_entries_1132_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v_mvarId_1140_; lean_object* v_fst_1141_; lean_object* v_snd_1142_; lean_object* v___x_1143_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref(v___x_1138_);
v_mvarId_1140_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_mvarId_1140_);
lean_dec(v___x_1130_);
v_fst_1141_ = lean_ctor_get(v_a_1139_, 0);
lean_inc(v_fst_1141_);
v_snd_1142_ = lean_ctor_get(v_a_1139_, 1);
lean_inc(v_snd_1142_);
lean_dec(v_a_1139_);
v___x_1143_ = l_Lean_MVarId_assertHypotheses(v_mvarId_1140_, v_fst_1141_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v_snd_1145_; lean_object* v_fst_1146_; lean_object* v___x_1147_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref(v___x_1143_);
v_snd_1145_ = lean_ctor_get(v_a_1144_, 1);
lean_inc(v_snd_1145_);
lean_dec(v_a_1144_);
v_fst_1146_ = lean_ctor_get(v_snd_1142_, 0);
lean_inc(v_fst_1146_);
lean_dec(v_snd_1142_);
v___x_1147_ = l_Lean_MVarId_tryClearMany(v_snd_1145_, v_fst_1146_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v_fst_1146_);
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
lean_dec(v_snd_1142_);
v_a_1165_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1143_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1143_);
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
lean_dec(v___x_1130_);
v_a_1173_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1138_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1138_);
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
v_ref_1289_ = lean_ctor_get(v___y_1286_, 5);
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
lean_dec_ref(v_a_1320_);
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
