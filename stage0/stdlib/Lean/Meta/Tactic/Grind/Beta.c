// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Beta
// Imports: public import Lean.Meta.Tactic.Grind.Types
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_getEqcLambdas___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_getEqcLambdas___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getEqcLambdas___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_getEqcLambdas___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.Tactic.Grind.Types"};
static const lean_object* l_Lean_Meta_Grind_getEqcLambdas___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getEqcLambdas___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_getEqcLambdas___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.Grind.foldEqc"};
static const lean_object* l_Lean_Meta_Grind_getEqcLambdas___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getEqcLambdas___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_getEqcLambdas___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Grind_getEqcLambdas___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getEqcLambdas___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_getEqcLambdas___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getEqcLambdas___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEqcLambdas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEqcLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getFnRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getFnRoots___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "beta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(12, 31, 7, 123, 15, 248, 150, 29)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", using "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(lean_object* v_msg_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v_toApplicative_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_87_; 
v___x_18_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0, &l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0);
v___x_19_ = l_StateRefT_x27_instMonad___redArg(v___x_18_);
v_toApplicative_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v___x_19_, 1);
lean_dec(v_unused_88_);
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_87_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_toApplicative_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_87_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v_toFunctor_24_; lean_object* v_toSeq_25_; lean_object* v_toSeqLeft_26_; lean_object* v_toSeqRight_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_85_; 
v_toFunctor_24_ = lean_ctor_get(v_toApplicative_20_, 0);
v_toSeq_25_ = lean_ctor_get(v_toApplicative_20_, 2);
v_toSeqLeft_26_ = lean_ctor_get(v_toApplicative_20_, 3);
v_toSeqRight_27_ = lean_ctor_get(v_toApplicative_20_, 4);
v_isSharedCheck_85_ = !lean_is_exclusive(v_toApplicative_20_);
if (v_isSharedCheck_85_ == 0)
{
lean_object* v_unused_86_; 
v_unused_86_ = lean_ctor_get(v_toApplicative_20_, 1);
lean_dec(v_unused_86_);
v___x_29_ = v_toApplicative_20_;
v_isShared_30_ = v_isSharedCheck_85_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_toSeqRight_27_);
lean_inc(v_toSeqLeft_26_);
lean_inc(v_toSeq_25_);
lean_inc(v_toFunctor_24_);
lean_dec(v_toApplicative_20_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_85_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___f_31_; lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___f_34_; lean_object* v___x_35_; lean_object* v___f_36_; lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___x_40_; 
v___f_31_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__1));
v___f_32_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__2));
lean_inc_ref(v_toFunctor_24_);
v___f_33_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_33_, 0, v_toFunctor_24_);
v___f_34_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_34_, 0, v_toFunctor_24_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v___f_33_);
lean_ctor_set(v___x_35_, 1, v___f_34_);
v___f_36_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_36_, 0, v_toSeqRight_27_);
v___f_37_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_37_, 0, v_toSeqLeft_26_);
v___f_38_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_38_, 0, v_toSeq_25_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 4, v___f_36_);
lean_ctor_set(v___x_29_, 3, v___f_37_);
lean_ctor_set(v___x_29_, 2, v___f_38_);
lean_ctor_set(v___x_29_, 1, v___f_31_);
lean_ctor_set(v___x_29_, 0, v___x_35_);
v___x_40_ = v___x_29_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v___f_31_);
lean_ctor_set(v_reuseFailAlloc_84_, 2, v___f_38_);
lean_ctor_set(v_reuseFailAlloc_84_, 3, v___f_37_);
lean_ctor_set(v_reuseFailAlloc_84_, 4, v___f_36_);
v___x_40_ = v_reuseFailAlloc_84_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_42_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___f_32_);
lean_ctor_set(v___x_22_, 0, v___x_40_);
v___x_42_ = v___x_22_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___f_32_);
v___x_42_ = v_reuseFailAlloc_83_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_43_; lean_object* v_toApplicative_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_81_; 
v___x_43_ = l_StateRefT_x27_instMonad___redArg(v___x_42_);
v_toApplicative_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_81_ == 0)
{
lean_object* v_unused_82_; 
v_unused_82_ = lean_ctor_get(v___x_43_, 1);
lean_dec(v_unused_82_);
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_81_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_toApplicative_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_81_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_toFunctor_48_; lean_object* v_toSeq_49_; lean_object* v_toSeqLeft_50_; lean_object* v_toSeqRight_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_79_; 
v_toFunctor_48_ = lean_ctor_get(v_toApplicative_44_, 0);
v_toSeq_49_ = lean_ctor_get(v_toApplicative_44_, 2);
v_toSeqLeft_50_ = lean_ctor_get(v_toApplicative_44_, 3);
v_toSeqRight_51_ = lean_ctor_get(v_toApplicative_44_, 4);
v_isSharedCheck_79_ = !lean_is_exclusive(v_toApplicative_44_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v_toApplicative_44_, 1);
lean_dec(v_unused_80_);
v___x_53_ = v_toApplicative_44_;
v_isShared_54_ = v_isSharedCheck_79_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_toSeqRight_51_);
lean_inc(v_toSeqLeft_50_);
lean_inc(v_toSeq_49_);
lean_inc(v_toFunctor_48_);
lean_dec(v_toApplicative_44_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_79_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___f_60_; lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___x_64_; 
v___f_55_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__3));
v___f_56_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__4));
lean_inc_ref(v_toFunctor_48_);
v___f_57_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_57_, 0, v_toFunctor_48_);
v___f_58_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_58_, 0, v_toFunctor_48_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___f_57_);
lean_ctor_set(v___x_59_, 1, v___f_58_);
v___f_60_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_60_, 0, v_toSeqRight_51_);
v___f_61_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_61_, 0, v_toSeqLeft_50_);
v___f_62_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_62_, 0, v_toSeq_49_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 4, v___f_60_);
lean_ctor_set(v___x_53_, 3, v___f_61_);
lean_ctor_set(v___x_53_, 2, v___f_62_);
lean_ctor_set(v___x_53_, 1, v___f_55_);
lean_ctor_set(v___x_53_, 0, v___x_59_);
v___x_64_ = v___x_53_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___f_55_);
lean_ctor_set(v_reuseFailAlloc_78_, 2, v___f_62_);
lean_ctor_set(v_reuseFailAlloc_78_, 3, v___f_61_);
lean_ctor_set(v_reuseFailAlloc_78_, 4, v___f_60_);
v___x_64_ = v_reuseFailAlloc_78_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_66_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v___f_56_);
lean_ctor_set(v___x_46_, 0, v___x_64_);
v___x_66_ = v___x_46_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v___f_56_);
v___x_66_ = v_reuseFailAlloc_77_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_2194__overap_75_; lean_object* v___x_76_; 
v___x_67_ = l_StateRefT_x27_instMonad___redArg(v___x_66_);
v___x_68_ = l_ReaderT_instMonad___redArg(v___x_67_);
v___x_69_ = l_StateRefT_x27_instMonad___redArg(v___x_68_);
v___x_70_ = l_ReaderT_instMonad___redArg(v___x_69_);
v___x_71_ = l_ReaderT_instMonad___redArg(v___x_70_);
v___x_72_ = l_StateRefT_x27_instMonad___redArg(v___x_71_);
v___x_73_ = lean_box(0);
v___x_74_ = l_instInhabitedOfMonad___redArg(v___x_72_, v___x_73_);
v___x_2194__overap_75_ = lean_panic_fn(v___x_74_, v_msg_6_);
lean_inc(v___y_16_);
lean_inc_ref(v___y_15_);
lean_inc(v___y_14_);
lean_inc_ref(v___y_13_);
lean_inc(v___y_12_);
lean_inc_ref(v___y_11_);
lean_inc(v___y_10_);
lean_inc_ref(v___y_9_);
lean_inc(v___y_8_);
lean_inc(v___y_7_);
v___x_76_ = lean_apply_11(v___x_2194__overap_75_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, lean_box(0));
return v___x_76_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___boxed(lean_object* v_msg_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(v_msg_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec(v___y_90_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(lean_object* v___x_102_, lean_object* v_b_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; lean_object* v_snd_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_160_; 
v___x_110_ = lean_st_ref_get(v___y_104_);
v_snd_111_ = lean_ctor_get(v_b_103_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_b_103_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v_b_103_, 0);
lean_dec(v_unused_161_);
v___x_113_ = v_b_103_;
v_isShared_114_ = v_isSharedCheck_160_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_snd_111_);
lean_dec(v_b_103_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_160_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_159_; 
v_fst_115_ = lean_ctor_get(v_snd_111_, 0);
v_snd_116_ = lean_ctor_get(v_snd_111_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_snd_111_);
if (v_isSharedCheck_159_ == 0)
{
v___x_118_ = v_snd_111_;
v_isShared_119_ = v_isSharedCheck_159_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
lean_dec(v_snd_111_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_159_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; 
lean_inc(v_fst_115_);
v___x_120_ = l_Lean_Meta_Grind_Goal_getENode(v___x_110_, v_fst_115_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_150_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_150_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_150_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_150_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v_self_125_; lean_object* v_next_126_; lean_object* v___x_127_; lean_object* v_a_129_; uint8_t v___x_148_; 
v_self_125_ = lean_ctor_get(v_a_121_, 0);
lean_inc_ref(v_self_125_);
v_next_126_ = lean_ctor_get(v_a_121_, 1);
lean_inc_ref(v_next_126_);
lean_dec(v_a_121_);
v___x_127_ = lean_box(0);
v___x_148_ = l_Lean_Expr_isLambda(v_self_125_);
if (v___x_148_ == 0)
{
lean_dec_ref(v_self_125_);
v_a_129_ = v_snd_116_;
goto v___jp_128_;
}
else
{
lean_object* v___x_149_; 
v___x_149_ = lean_array_push(v_snd_116_, v_self_125_);
v_a_129_ = v___x_149_;
goto v___jp_128_;
}
v___jp_128_:
{
uint8_t v___x_130_; 
v___x_130_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_126_, v___x_102_);
if (v___x_130_ == 0)
{
lean_object* v___x_132_; 
lean_del_object(v___x_123_);
lean_dec(v_fst_115_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_a_129_);
lean_ctor_set(v___x_118_, 0, v_next_126_);
v___x_132_ = v___x_118_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_next_126_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_a_129_);
v___x_132_ = v_reuseFailAlloc_137_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_134_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_132_);
lean_ctor_set(v___x_113_, 0, v___x_127_);
v___x_134_ = v___x_113_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_136_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
v_b_103_ = v___x_134_;
goto _start;
}
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_140_; 
lean_dec_ref(v_next_126_);
lean_inc_ref(v_a_129_);
v___x_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_138_, 0, v_a_129_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_a_129_);
v___x_140_ = v___x_118_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_a_129_);
v___x_140_ = v_reuseFailAlloc_147_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_140_);
lean_ctor_set(v___x_113_, 0, v___x_138_);
v___x_142_ = v___x_113_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_146_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_142_);
v___x_144_ = v___x_123_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_del_object(v___x_118_);
lean_dec(v_snd_116_);
lean_dec(v_fst_115_);
lean_del_object(v___x_113_);
v_a_151_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_120_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_120_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg___boxed(lean_object* v___x_162_, lean_object* v_b_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v___x_162_, v_b_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___x_162_);
return v_res_170_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_176_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__3));
v___x_177_ = lean_unsigned_to_nat(2u);
v___x_178_ = lean_unsigned_to_nat(1567u);
v___x_179_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__2));
v___x_180_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__1));
v___x_181_ = l_mkPanicMessageWithDecl(v___x_180_, v___x_179_, v___x_178_, v___x_177_, v___x_176_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEqcLambdas(lean_object* v_root_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
uint8_t v_hasLambdas_194_; 
v_hasLambdas_194_ = lean_ctor_get_uint8(v_root_182_, sizeof(void*)*11 + 3);
if (v_hasLambdas_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
else
{
lean_object* v_self_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_self_197_ = lean_ctor_get(v_root_182_, 0);
v___x_198_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_199_ = lean_box(0);
lean_inc_ref(v_self_197_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v_self_197_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v_self_197_, v___x_201_, v_a_183_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_232_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_232_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_232_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_232_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v_fst_207_; 
v_fst_207_ = lean_ctor_get(v_a_203_, 0);
if (lean_obj_tag(v_fst_207_) == 0)
{
lean_object* v_snd_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
lean_del_object(v___x_205_);
v_snd_208_ = lean_ctor_get(v_a_203_, 1);
lean_inc(v_snd_208_);
lean_dec(v_a_203_);
v___x_209_ = lean_obj_once(&l_Lean_Meta_Grind_getEqcLambdas___closed__4, &l_Lean_Meta_Grind_getEqcLambdas___closed__4_once, _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4);
v___x_210_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(v___x_209_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_218_; 
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v___x_210_, 0);
lean_dec(v_unused_219_);
v___x_212_ = v___x_210_;
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
else
{
lean_dec(v___x_210_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_snd_214_; lean_object* v___x_216_; 
v_snd_214_ = lean_ctor_get(v_snd_208_, 1);
lean_inc(v_snd_214_);
lean_dec(v_snd_208_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v_snd_214_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_snd_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec(v_snd_208_);
v_a_220_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_210_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_210_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_object* v_val_228_; lean_object* v___x_230_; 
lean_inc_ref(v_fst_207_);
lean_dec(v_a_203_);
v_val_228_ = lean_ctor_get(v_fst_207_, 0);
lean_inc(v_val_228_);
lean_dec_ref(v_fst_207_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v_val_228_);
v___x_230_ = v___x_205_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_val_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
v_a_233_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_202_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_202_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEqcLambdas___boxed(lean_object* v_root_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Meta_Grind_getEqcLambdas(v_root_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_root_241_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(lean_object* v___x_254_, lean_object* v_b_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v___x_254_, v_b_255_, v___y_256_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___boxed(lean_object* v___x_268_, lean_object* v_b_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(v___x_268_, v_b_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___x_268_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(lean_object* v___y_285_, lean_object* v_as_286_, size_t v_sz_287_, size_t v_i_288_, lean_object* v_b_289_){
_start:
{
uint8_t v___x_290_; 
v___x_290_ = lean_usize_dec_lt(v_i_288_, v_sz_287_);
if (v___x_290_ == 0)
{
return v_b_289_;
}
else
{
lean_object* v___x_291_; lean_object* v_a_292_; uint8_t v___x_293_; 
lean_dec_ref(v_b_289_);
v___x_291_ = lean_box(0);
v_a_292_ = lean_array_uget_borrowed(v_as_286_, v_i_288_);
v___x_293_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_292_, v___y_285_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; size_t v___x_295_; size_t v___x_296_; 
v___x_294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0));
v___x_295_ = ((size_t)1ULL);
v___x_296_ = lean_usize_add(v_i_288_, v___x_295_);
v_i_288_ = v___x_296_;
v_b_289_ = v___x_294_;
goto _start;
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
lean_inc(v_a_292_);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v_a_292_);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_291_);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___boxed(lean_object* v___y_301_, lean_object* v_as_302_, lean_object* v_sz_303_, lean_object* v_i_304_, lean_object* v_b_305_){
_start:
{
size_t v_sz_boxed_306_; size_t v_i_boxed_307_; lean_object* v_res_308_; 
v_sz_boxed_306_ = lean_unbox_usize(v_sz_303_);
lean_dec(v_sz_303_);
v_i_boxed_307_ = lean_unbox_usize(v_i_304_);
lean_dec(v_i_304_);
v_res_308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(v___y_301_, v_as_302_, v_sz_boxed_306_, v_i_boxed_307_, v_b_305_);
lean_dec_ref(v_as_302_);
lean_dec_ref(v___y_301_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(lean_object* v_e_312_, lean_object* v_b_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_320_; lean_object* v_snd_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_383_; 
v___x_320_ = lean_st_ref_get(v___y_314_);
v_snd_321_ = lean_ctor_get(v_b_313_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_b_313_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_b_313_, 0);
lean_dec(v_unused_384_);
v___x_323_ = v_b_313_;
v_isShared_324_ = v_isSharedCheck_383_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_snd_321_);
lean_dec(v_b_313_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_383_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v_fst_325_; lean_object* v_snd_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_382_; 
v_fst_325_ = lean_ctor_get(v_snd_321_, 0);
v_snd_326_ = lean_ctor_get(v_snd_321_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v_snd_321_);
if (v_isSharedCheck_382_ == 0)
{
v___x_328_ = v_snd_321_;
v_isShared_329_ = v_isSharedCheck_382_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_snd_326_);
lean_inc(v_fst_325_);
lean_dec(v_snd_321_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_382_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; 
lean_inc(v_fst_325_);
v___x_330_ = l_Lean_Meta_Grind_Goal_getENode(v___x_320_, v_fst_325_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_373_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_373_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_373_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_373_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v_self_336_; lean_object* v_next_337_; lean_object* v___x_338_; lean_object* v_a_340_; lean_object* v___y_360_; lean_object* v___y_363_; lean_object* v_fn_370_; lean_object* v___x_371_; 
v___x_335_ = lean_st_ref_get(v___y_314_);
v_self_336_ = lean_ctor_get(v_a_331_, 0);
lean_inc_ref(v_self_336_);
v_next_337_ = lean_ctor_get(v_a_331_, 1);
lean_inc_ref(v_next_337_);
lean_dec(v_a_331_);
v___x_338_ = lean_box(0);
v_fn_370_ = l_Lean_Expr_getAppFn(v_self_336_);
lean_dec_ref(v_self_336_);
v___x_371_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_335_, v_fn_370_);
if (lean_obj_tag(v___x_371_) == 0)
{
v___y_363_ = v_fn_370_;
goto v___jp_362_;
}
else
{
lean_object* v_val_372_; 
lean_dec_ref(v_fn_370_);
v_val_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_val_372_);
lean_dec_ref(v___x_371_);
v___y_363_ = v_val_372_;
goto v___jp_362_;
}
v___jp_339_:
{
uint8_t v___x_341_; 
v___x_341_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_337_, v_e_312_);
if (v___x_341_ == 0)
{
lean_object* v___x_343_; 
lean_del_object(v___x_333_);
lean_dec(v_fst_325_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v_a_340_);
lean_ctor_set(v___x_328_, 0, v_next_337_);
v___x_343_ = v___x_328_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_next_337_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_a_340_);
v___x_343_ = v_reuseFailAlloc_348_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_343_);
lean_ctor_set(v___x_323_, 0, v___x_338_);
v___x_345_ = v___x_323_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v___x_343_);
v___x_345_ = v_reuseFailAlloc_347_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
v_b_313_ = v___x_345_;
goto _start;
}
}
}
else
{
lean_object* v___x_349_; lean_object* v___x_351_; 
lean_dec_ref(v_next_337_);
lean_inc_ref(v_a_340_);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v_a_340_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v_a_340_);
v___x_351_ = v___x_328_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_fst_325_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_a_340_);
v___x_351_ = v_reuseFailAlloc_358_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_353_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_351_);
lean_ctor_set(v___x_323_, 0, v___x_349_);
v___x_353_ = v___x_323_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_357_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_353_);
v___x_355_ = v___x_333_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
v___jp_359_:
{
lean_object* v___x_361_; 
v___x_361_ = lean_array_push(v_snd_326_, v___y_360_);
v_a_340_ = v___x_361_;
goto v___jp_339_;
}
v___jp_362_:
{
lean_object* v___x_364_; size_t v_sz_365_; size_t v___x_366_; lean_object* v___x_367_; lean_object* v_fst_368_; 
v___x_364_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0));
v_sz_365_ = lean_array_size(v_snd_326_);
v___x_366_ = ((size_t)0ULL);
v___x_367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(v___y_363_, v_snd_326_, v_sz_365_, v___x_366_, v___x_364_);
v_fst_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_fst_368_);
lean_dec_ref(v___x_367_);
if (lean_obj_tag(v_fst_368_) == 0)
{
v___y_360_ = v___y_363_;
goto v___jp_359_;
}
else
{
lean_object* v_val_369_; 
v_val_369_ = lean_ctor_get(v_fst_368_, 0);
lean_inc(v_val_369_);
lean_dec_ref(v_fst_368_);
if (lean_obj_tag(v_val_369_) == 0)
{
v___y_360_ = v___y_363_;
goto v___jp_359_;
}
else
{
lean_dec_ref(v_val_369_);
lean_dec_ref(v___y_363_);
v_a_340_ = v_snd_326_;
goto v___jp_339_;
}
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_del_object(v___x_328_);
lean_dec(v_snd_326_);
lean_dec(v_fst_325_);
lean_del_object(v___x_323_);
v_a_374_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_330_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_330_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___boxed(lean_object* v_e_385_, lean_object* v_b_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_385_, v_b_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v_e_385_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getFnRoots(lean_object* v_e_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_406_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_407_ = lean_box(0);
lean_inc_ref(v_e_394_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_e_394_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_394_, v___x_409_, v_a_395_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
lean_dec_ref(v_e_394_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_440_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_440_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_440_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_440_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v_fst_415_; 
v_fst_415_ = lean_ctor_get(v_a_411_, 0);
if (lean_obj_tag(v_fst_415_) == 0)
{
lean_object* v_snd_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_del_object(v___x_413_);
v_snd_416_ = lean_ctor_get(v_a_411_, 1);
lean_inc(v_snd_416_);
lean_dec(v_a_411_);
v___x_417_ = lean_obj_once(&l_Lean_Meta_Grind_getEqcLambdas___closed__4, &l_Lean_Meta_Grind_getEqcLambdas___closed__4_once, _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4);
v___x_418_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(v___x_417_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_426_; 
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; 
v_unused_427_ = lean_ctor_get(v___x_418_, 0);
lean_dec(v_unused_427_);
v___x_420_ = v___x_418_;
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
else
{
lean_dec(v___x_418_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_snd_422_; lean_object* v___x_424_; 
v_snd_422_ = lean_ctor_get(v_snd_416_, 1);
lean_inc(v_snd_422_);
lean_dec(v_snd_416_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v_snd_422_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_snd_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_snd_416_);
v_a_428_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_418_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_418_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
else
{
lean_object* v_val_436_; lean_object* v___x_438_; 
lean_inc_ref(v_fst_415_);
lean_dec(v_a_411_);
v_val_436_ = lean_ctor_get(v_fst_415_, 0);
lean_inc(v_val_436_);
lean_dec_ref(v_fst_415_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v_val_436_);
v___x_438_ = v___x_413_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_val_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_a_441_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_410_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_410_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getFnRoots___boxed(lean_object* v_e_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_Grind_getFnRoots(v_e_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec(v_a_450_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1(lean_object* v_e_462_, lean_object* v_b_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_462_, v_b_463_, v___y_464_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___boxed(lean_object* v_e_476_, lean_object* v_b_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1(v_e_476_, v_b_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v_e_476_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(lean_object* v_cls_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_options_496_; uint8_t v_hasTrace_497_; 
v_options_496_ = lean_ctor_get(v___y_494_, 2);
v_hasTrace_497_ = lean_ctor_get_uint8(v_options_496_, sizeof(void*)*1);
if (v_hasTrace_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v_cls_493_);
v___x_498_ = lean_box(v_hasTrace_497_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
else
{
lean_object* v_inheritedTraceOptions_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_inheritedTraceOptions_500_ = lean_ctor_get(v___y_494_, 13);
v___x_501_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1));
v___x_502_ = l_Lean_Name_append(v___x_501_, v_cls_493_);
v___x_503_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_500_, v_options_496_, v___x_502_);
lean_dec(v___x_502_);
v___x_504_ = lean_box(v___x_503_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___boxed(lean_object* v_cls_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v_cls_506_, v___y_507_);
lean_dec_ref(v___y_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(lean_object* v_cls_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v_cls_510_, v___y_519_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___boxed(lean_object* v_cls_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(v_cls_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
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
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2_spec__2(lean_object* v_msgData_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_542_; lean_object* v_env_543_; lean_object* v___x_544_; lean_object* v_mctx_545_; lean_object* v_lctx_546_; lean_object* v_options_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_542_ = lean_st_ref_get(v___y_540_);
v_env_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc_ref(v_env_543_);
lean_dec(v___x_542_);
v___x_544_ = lean_st_ref_get(v___y_538_);
v_mctx_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc_ref(v_mctx_545_);
lean_dec(v___x_544_);
v_lctx_546_ = lean_ctor_get(v___y_537_, 2);
v_options_547_ = lean_ctor_get(v___y_539_, 2);
lean_inc_ref(v_options_547_);
lean_inc_ref(v_lctx_546_);
v___x_548_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_548_, 0, v_env_543_);
lean_ctor_set(v___x_548_, 1, v_mctx_545_);
lean_ctor_set(v___x_548_, 2, v_lctx_546_);
lean_ctor_set(v___x_548_, 3, v_options_547_);
v___x_549_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v_msgData_536_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2_spec__2___boxed(lean_object* v_msgData_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2_spec__2(v_msgData_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
return v_res_557_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_558_; double v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_float_of_nat(v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(lean_object* v_cls_563_, lean_object* v_msg_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_ref_570_; lean_object* v___x_571_; lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_616_; 
v_ref_570_ = lean_ctor_get(v___y_567_, 5);
v___x_571_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2_spec__2(v_msg_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_616_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_616_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_616_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v_traceState_577_; lean_object* v_env_578_; lean_object* v_nextMacroScope_579_; lean_object* v_ngen_580_; lean_object* v_auxDeclNGen_581_; lean_object* v_cache_582_; lean_object* v_messages_583_; lean_object* v_infoState_584_; lean_object* v_snapshotTasks_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_615_; 
v___x_576_ = lean_st_ref_take(v___y_568_);
v_traceState_577_ = lean_ctor_get(v___x_576_, 4);
v_env_578_ = lean_ctor_get(v___x_576_, 0);
v_nextMacroScope_579_ = lean_ctor_get(v___x_576_, 1);
v_ngen_580_ = lean_ctor_get(v___x_576_, 2);
v_auxDeclNGen_581_ = lean_ctor_get(v___x_576_, 3);
v_cache_582_ = lean_ctor_get(v___x_576_, 5);
v_messages_583_ = lean_ctor_get(v___x_576_, 6);
v_infoState_584_ = lean_ctor_get(v___x_576_, 7);
v_snapshotTasks_585_ = lean_ctor_get(v___x_576_, 8);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_615_ == 0)
{
v___x_587_ = v___x_576_;
v_isShared_588_ = v_isSharedCheck_615_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_snapshotTasks_585_);
lean_inc(v_infoState_584_);
lean_inc(v_messages_583_);
lean_inc(v_cache_582_);
lean_inc(v_traceState_577_);
lean_inc(v_auxDeclNGen_581_);
lean_inc(v_ngen_580_);
lean_inc(v_nextMacroScope_579_);
lean_inc(v_env_578_);
lean_dec(v___x_576_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_615_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
uint64_t v_tid_589_; lean_object* v_traces_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_614_; 
v_tid_589_ = lean_ctor_get_uint64(v_traceState_577_, sizeof(void*)*1);
v_traces_590_ = lean_ctor_get(v_traceState_577_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_traceState_577_);
if (v_isSharedCheck_614_ == 0)
{
v___x_592_ = v_traceState_577_;
v_isShared_593_ = v_isSharedCheck_614_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_traces_590_);
lean_dec(v_traceState_577_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_614_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; double v___x_595_; uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_594_ = lean_box(0);
v___x_595_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__0);
v___x_596_ = 0;
v___x_597_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__1));
v___x_598_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_598_, 0, v_cls_563_);
lean_ctor_set(v___x_598_, 1, v___x_594_);
lean_ctor_set(v___x_598_, 2, v___x_597_);
lean_ctor_set_float(v___x_598_, sizeof(void*)*3, v___x_595_);
lean_ctor_set_float(v___x_598_, sizeof(void*)*3 + 8, v___x_595_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*3 + 16, v___x_596_);
v___x_599_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___closed__2));
v___x_600_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v_a_572_);
lean_ctor_set(v___x_600_, 2, v___x_599_);
lean_inc(v_ref_570_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v_ref_570_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_PersistentArray_push___redArg(v_traces_590_, v___x_601_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_602_);
v___x_604_ = v___x_592_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_602_);
lean_ctor_set_uint64(v_reuseFailAlloc_613_, sizeof(void*)*1, v_tid_589_);
v___x_604_ = v_reuseFailAlloc_613_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_606_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 4, v___x_604_);
v___x_606_ = v___x_587_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_env_578_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_nextMacroScope_579_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_ngen_580_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_auxDeclNGen_581_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_612_, 5, v_cache_582_);
lean_ctor_set(v_reuseFailAlloc_612_, 6, v_messages_583_);
lean_ctor_set(v_reuseFailAlloc_612_, 7, v_infoState_584_);
lean_ctor_set(v_reuseFailAlloc_612_, 8, v_snapshotTasks_585_);
v___x_606_ = v_reuseFailAlloc_612_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_607_ = lean_st_ref_set(v___y_568_, v___x_606_);
v___x_608_ = lean_box(0);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_608_);
v___x_610_ = v___x_574_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___boxed(lean_object* v_cls_617_, lean_object* v_msg_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_cls_617_, v_msg_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(lean_object* v_as_625_, size_t v_sz_626_, size_t v_i_627_, lean_object* v_b_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
uint8_t v___x_635_; 
v___x_635_ = lean_usize_dec_lt(v_i_627_, v_sz_626_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v_b_628_);
return v___x_636_;
}
else
{
lean_object* v_a_637_; lean_object* v___x_638_; 
v_a_637_ = lean_array_uget_borrowed(v_as_625_, v_i_627_);
v___x_638_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_637_, v___y_629_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v_fst_640_; lean_object* v_snd_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_664_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref(v___x_638_);
v_fst_640_ = lean_ctor_get(v_b_628_, 0);
v_snd_641_ = lean_ctor_get(v_b_628_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_b_628_);
if (v_isSharedCheck_664_ == 0)
{
v___x_643_ = v_b_628_;
v_isShared_644_ = v_isSharedCheck_664_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_snd_641_);
lean_inc(v_fst_640_);
lean_dec(v_b_628_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_664_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___y_646_; uint8_t v___x_663_; 
v___x_663_ = lean_nat_dec_le(v_fst_640_, v_a_639_);
if (v___x_663_ == 0)
{
lean_dec(v_a_639_);
v___y_646_ = v_fst_640_;
goto v___jp_645_;
}
else
{
lean_dec(v_fst_640_);
v___y_646_ = v_a_639_;
goto v___jp_645_;
}
v___jp_645_:
{
lean_object* v___x_647_; 
lean_inc(v_a_637_);
v___x_647_ = l_Lean_Meta_mkCongrFun(v_snd_641_, v_a_637_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_650_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref(v___x_647_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v_a_648_);
lean_ctor_set(v___x_643_, 0, v___y_646_);
v___x_650_ = v___x_643_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___y_646_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_a_648_);
v___x_650_ = v_reuseFailAlloc_654_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
size_t v___x_651_; size_t v___x_652_; 
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_add(v_i_627_, v___x_651_);
v_i_627_ = v___x_652_;
v_b_628_ = v___x_650_;
goto _start;
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec(v___y_646_);
lean_del_object(v___x_643_);
v_a_655_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_647_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_647_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v_b_628_);
v_a_665_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_638_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_638_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg___boxed(lean_object* v_as_673_, lean_object* v_sz_674_, lean_object* v_i_675_, lean_object* v_b_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
size_t v_sz_boxed_683_; size_t v_i_boxed_684_; lean_object* v_res_685_; 
v_sz_boxed_683_ = lean_unbox_usize(v_sz_674_);
lean_dec(v_sz_674_);
v_i_boxed_684_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_as_673_, v_sz_boxed_683_, v_i_boxed_684_, v_b_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v_as_673_);
return v_res_685_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3));
v___x_693_ = l_Lean_stringToMessageData(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(lean_object* v_args_694_, lean_object* v_f_695_, lean_object* v_as_696_, size_t v_sz_697_, size_t v_i_698_, lean_object* v_b_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_a_712_; uint8_t v___x_716_; 
v___x_716_ = lean_usize_dec_lt(v_i_698_, v_sz_697_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
lean_dec_ref(v_f_695_);
lean_dec_ref(v_args_694_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_b_699_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; lean_object* v_a_719_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_718_ = lean_box(0);
v_a_719_ = lean_array_uget_borrowed(v_as_696_, v_i_698_);
lean_inc_ref(v_args_694_);
lean_inc(v_a_719_);
v___x_738_ = l_Lean_Expr_beta(v_a_719_, v_args_694_);
v___x_739_ = l_Lean_Expr_isLambda(v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_719_, v___y_700_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref(v___x_740_);
v___x_742_ = l_Lean_Meta_Grind_getGeneration___redArg(v_f_695_, v___y_700_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___y_745_; uint8_t v___x_820_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref(v___x_742_);
v___x_820_ = lean_nat_dec_le(v_a_741_, v_a_743_);
if (v___x_820_ == 0)
{
lean_dec(v_a_743_);
v___y_745_ = v_a_741_;
goto v___jp_744_;
}
else
{
lean_dec(v_a_741_);
v___y_745_ = v_a_743_;
goto v___jp_744_;
}
v___jp_744_:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_inc_ref(v_f_695_);
v___x_746_ = l_Lean_mkAppN(v_f_695_, v_args_694_);
lean_inc(v_a_719_);
lean_inc_ref(v_f_695_);
v___x_747_ = l_Lean_Meta_Grind_hasSameType(v_f_695_, v_a_719_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; uint8_t v___x_749_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref(v___x_747_);
v___x_749_ = lean_unbox(v_a_748_);
lean_dec(v_a_748_);
if (v___x_749_ == 0)
{
lean_dec_ref(v___x_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___x_738_);
v_a_712_ = v___x_718_;
goto v___jp_711_;
}
else
{
lean_object* v___x_750_; 
lean_inc(v___y_709_);
lean_inc_ref(v___y_708_);
lean_inc(v___y_707_);
lean_inc_ref(v___y_706_);
lean_inc(v___y_705_);
lean_inc_ref(v___y_704_);
lean_inc(v___y_703_);
lean_inc_ref(v___y_702_);
lean_inc(v___y_701_);
lean_inc(v___y_700_);
lean_inc(v_a_719_);
lean_inc_ref(v_f_695_);
v___x_750_ = lean_grind_mk_eq_proof(v_f_695_, v_a_719_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_752_; size_t v_sz_753_; size_t v___x_754_; lean_object* v___x_755_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref(v___x_750_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___y_745_);
lean_ctor_set(v___x_752_, 1, v_a_751_);
v_sz_753_ = lean_array_size(v_args_694_);
v___x_754_ = ((size_t)0ULL);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_args_694_, v_sz_753_, v___x_754_, v___x_752_, v___y_700_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_757_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref(v___x_755_);
v___x_757_ = l_Lean_Meta_mkEq(v___x_746_, v___x_738_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref(v___x_757_);
v___x_759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2));
v___x_760_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v___x_759_, v___y_708_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; uint8_t v___x_762_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref(v___x_760_);
v___x_762_ = lean_unbox(v_a_761_);
lean_dec(v_a_761_);
if (v___x_762_ == 0)
{
lean_object* v_fst_763_; lean_object* v_snd_764_; 
v_fst_763_ = lean_ctor_get(v_a_756_, 0);
lean_inc(v_fst_763_);
v_snd_764_ = lean_ctor_get(v_a_756_, 1);
lean_inc(v_snd_764_);
lean_dec(v_a_756_);
v___y_721_ = v_fst_763_;
v___y_722_ = v_snd_764_;
v___y_723_ = v_a_758_;
v___y_724_ = v___y_700_;
v___y_725_ = v___y_701_;
v___y_726_ = v___y_702_;
v___y_727_ = v___y_703_;
v___y_728_ = v___y_704_;
v___y_729_ = v___y_705_;
v___y_730_ = v___y_706_;
v___y_731_ = v___y_707_;
v___y_732_ = v___y_708_;
v___y_733_ = v___y_709_;
goto v___jp_720_;
}
else
{
lean_object* v_fst_765_; lean_object* v_snd_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_779_; 
v_fst_765_ = lean_ctor_get(v_a_756_, 0);
v_snd_766_ = lean_ctor_get(v_a_756_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_a_756_);
if (v_isSharedCheck_779_ == 0)
{
v___x_768_ = v_a_756_;
v_isShared_769_ = v_isSharedCheck_779_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_snd_766_);
lean_inc(v_fst_765_);
lean_dec(v_a_756_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_779_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Meta_Grind_updateLastTag(v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
lean_dec_ref(v___x_770_);
lean_inc(v_a_758_);
v___x_771_ = l_Lean_MessageData_ofExpr(v_a_758_);
v___x_772_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4);
if (v_isShared_769_ == 0)
{
lean_ctor_set_tag(v___x_768_, 7);
lean_ctor_set(v___x_768_, 1, v___x_772_);
lean_ctor_set(v___x_768_, 0, v___x_771_);
v___x_774_ = v___x_768_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_772_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_inc(v_a_719_);
v___x_775_ = l_Lean_MessageData_ofExpr(v_a_719_);
v___x_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v___x_759_, v___x_776_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_dec_ref(v___x_777_);
v___y_721_ = v_fst_765_;
v___y_722_ = v_snd_766_;
v___y_723_ = v_a_758_;
v___y_724_ = v___y_700_;
v___y_725_ = v___y_701_;
v___y_726_ = v___y_702_;
v___y_727_ = v___y_703_;
v___y_728_ = v___y_704_;
v___y_729_ = v___y_705_;
v___y_730_ = v___y_706_;
v___y_731_ = v___y_707_;
v___y_732_ = v___y_708_;
v___y_733_ = v___y_709_;
goto v___jp_720_;
}
else
{
lean_dec(v_snd_766_);
lean_dec(v_fst_765_);
lean_dec(v_a_758_);
lean_dec_ref(v_f_695_);
lean_dec_ref(v_args_694_);
return v___x_777_;
}
}
}
else
{
lean_del_object(v___x_768_);
lean_dec(v_snd_766_);
lean_dec(v_fst_765_);
lean_dec(v_a_758_);
lean_dec_ref(v_f_695_);
lean_dec_ref(v_args_694_);
return v___x_770_;
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec(v_a_758_);
lean_dec(v_a_756_);
lean_dec_ref(v_f_695_);
lean_dec_ref(v_args_694_);
v_a_780_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_760_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_760_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v_a_756_);
lean_dec_ref(v_f_695_);
lean_dec_ref(v_args_694_);
v_a_788_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_757_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_757_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v___x_746_);
lean_dec_ref(v___x_738_);
lean_dec_ref(v_f_695_);
lean_dec_ref(v_args_694_);
v_a_796_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_755_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_755_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v___x_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___x_738_);
lean_dec_ref(v_f_695_);
lean_dec_ref(v_args_694_);
v_a_804_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_750_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_750_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v___x_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___x_738_);
lean_dec_ref(v_f_695_);
lean_dec_ref(v_args_694_);
v_a_812_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_747_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_747_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_a_741_);
lean_dec_ref(v___x_738_);
lean_dec_ref(v_f_695_);
lean_dec_ref(v_args_694_);
v_a_821_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_742_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_742_);
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
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec_ref(v___x_738_);
lean_dec_ref(v_f_695_);
lean_dec_ref(v_args_694_);
v_a_829_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_740_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_740_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_dec_ref(v___x_738_);
v_a_712_ = v___x_718_;
goto v___jp_711_;
}
v___jp_720_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_734_ = lean_unsigned_to_nat(1u);
v___x_735_ = lean_nat_add(v___y_721_, v___x_734_);
lean_dec(v___y_721_);
lean_inc(v_a_719_);
v___x_736_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_736_, 0, v_a_719_);
v___x_737_ = l_Lean_Meta_Grind_addNewRawFact(v___y_722_, v___y_723_, v___x_735_, v___x_736_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_dec_ref(v___x_737_);
v_a_712_ = v___x_718_;
goto v___jp_711_;
}
else
{
lean_dec_ref(v_f_695_);
lean_dec_ref(v_args_694_);
return v___x_737_;
}
}
}
v___jp_711_:
{
size_t v___x_713_; size_t v___x_714_; 
v___x_713_ = ((size_t)1ULL);
v___x_714_ = lean_usize_add(v_i_698_, v___x_713_);
v_i_698_ = v___x_714_;
v_b_699_ = v_a_712_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___boxed(lean_object** _args){
lean_object* v_args_837_ = _args[0];
lean_object* v_f_838_ = _args[1];
lean_object* v_as_839_ = _args[2];
lean_object* v_sz_840_ = _args[3];
lean_object* v_i_841_ = _args[4];
lean_object* v_b_842_ = _args[5];
lean_object* v___y_843_ = _args[6];
lean_object* v___y_844_ = _args[7];
lean_object* v___y_845_ = _args[8];
lean_object* v___y_846_ = _args[9];
lean_object* v___y_847_ = _args[10];
lean_object* v___y_848_ = _args[11];
lean_object* v___y_849_ = _args[12];
lean_object* v___y_850_ = _args[13];
lean_object* v___y_851_ = _args[14];
lean_object* v___y_852_ = _args[15];
lean_object* v___y_853_ = _args[16];
_start:
{
size_t v_sz_boxed_854_; size_t v_i_boxed_855_; lean_object* v_res_856_; 
v_sz_boxed_854_ = lean_unbox_usize(v_sz_840_);
lean_dec(v_sz_840_);
v_i_boxed_855_ = lean_unbox_usize(v_i_841_);
lean_dec(v_i_841_);
v_res_856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(v_args_837_, v_f_838_, v_as_839_, v_sz_boxed_854_, v_i_boxed_855_, v_b_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v_as_839_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs(lean_object* v_lams_857_, lean_object* v_f_858_, lean_object* v_args_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_871_ = lean_array_get_size(v_args_859_);
v___x_872_ = lean_unsigned_to_nat(0u);
v___x_873_ = lean_nat_dec_eq(v___x_871_, v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; size_t v_sz_875_; size_t v___x_876_; lean_object* v___x_877_; 
v___x_874_ = lean_box(0);
v_sz_875_ = lean_array_size(v_lams_857_);
v___x_876_ = ((size_t)0ULL);
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(v_args_859_, v_f_858_, v_lams_857_, v_sz_875_, v___x_876_, v___x_874_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v___x_877_, 0);
lean_dec(v_unused_885_);
v___x_879_ = v___x_877_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_dec(v___x_877_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_874_);
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_874_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
else
{
return v___x_877_;
}
}
else
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec_ref(v_args_859_);
lean_dec_ref(v_f_858_);
v___x_886_ = lean_box(0);
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs___boxed(lean_object* v_lams_888_, lean_object* v_f_889_, lean_object* v_args_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_888_, v_f_889_, v_args_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_lams_888_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(lean_object* v_as_903_, size_t v_sz_904_, size_t v_i_905_, lean_object* v_b_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_as_903_, v_sz_904_, v_i_905_, v_b_906_, v___y_907_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___boxed(lean_object* v_as_919_, lean_object* v_sz_920_, lean_object* v_i_921_, lean_object* v_b_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
size_t v_sz_boxed_934_; size_t v_i_boxed_935_; lean_object* v_res_936_; 
v_sz_boxed_934_ = lean_unbox_usize(v_sz_920_);
lean_dec(v_sz_920_);
v_i_boxed_935_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(v_as_919_, v_sz_boxed_934_, v_i_boxed_935_, v_b_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v_as_919_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(lean_object* v_cls_937_, lean_object* v_msg_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_cls_937_, v_msg_938_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___boxed(lean_object* v_cls_951_, lean_object* v_msg_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(v_cls_951_, v_msg_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec(v___y_953_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(lean_object* v_f_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_f_965_, v_a_966_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1010_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_1010_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1010_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; 
if (lean_obj_tag(v_a_978_) == 1)
{
lean_object* v_val_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1009_; 
v_val_1000_ = lean_ctor_get(v_a_978_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_a_978_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1002_ = v_a_978_;
v_isShared_1003_ = v_isSharedCheck_1009_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_val_1000_);
lean_dec(v_a_978_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1009_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
uint8_t v_hasLambdas_1004_; 
v_hasLambdas_1004_ = lean_ctor_get_uint8(v_val_1000_, sizeof(void*)*11 + 3);
lean_dec(v_val_1000_);
if (v_hasLambdas_1004_ == 0)
{
lean_del_object(v___x_1002_);
v___y_983_ = v_a_966_;
v___y_984_ = v_a_967_;
v___y_985_ = v_a_968_;
v___y_986_ = v_a_969_;
v___y_987_ = v_a_970_;
v___y_988_ = v_a_971_;
v___y_989_ = v_a_972_;
v___y_990_ = v_a_973_;
v___y_991_ = v_a_974_;
v___y_992_ = v_a_975_;
goto v___jp_982_;
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
lean_del_object(v___x_980_);
v___x_1005_ = lean_box(v_hasLambdas_1004_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1005_);
v___x_1007_ = v___x_1002_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_dec(v_a_978_);
v___y_983_ = v_a_966_;
v___y_984_ = v_a_967_;
v___y_985_ = v_a_968_;
v___y_986_ = v_a_969_;
v___y_987_ = v_a_970_;
v___y_988_ = v_a_971_;
v___y_989_ = v_a_972_;
v___y_990_ = v_a_973_;
v___y_991_ = v_a_974_;
v___y_992_ = v_a_975_;
goto v___jp_982_;
}
v___jp_982_:
{
if (lean_obj_tag(v_f_965_) == 5)
{
lean_object* v_fn_993_; 
lean_del_object(v___x_980_);
v_fn_993_ = lean_ctor_get(v_f_965_, 0);
v_f_965_ = v_fn_993_;
v_a_966_ = v___y_983_;
v_a_967_ = v___y_984_;
v_a_968_ = v___y_985_;
v_a_969_ = v___y_986_;
v_a_970_ = v___y_987_;
v_a_971_ = v___y_988_;
v_a_972_ = v___y_989_;
v_a_973_ = v___y_990_;
v_a_974_ = v___y_991_;
v_a_975_ = v___y_992_;
goto _start;
}
else
{
uint8_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_995_ = 0;
v___x_996_ = lean_box(v___x_995_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_996_);
v___x_998_ = v___x_980_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
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
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_977_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_977_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go___boxed(lean_object* v_f_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(v_f_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_f_1019_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(lean_object* v_e_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
if (lean_obj_tag(v_e_1032_) == 5)
{
lean_object* v_fn_1044_; lean_object* v___x_1045_; 
v_fn_1044_ = lean_ctor_get(v_e_1032_, 0);
v___x_1045_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(v_fn_1044_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
return v___x_1045_;
}
else
{
uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = 0;
v___x_1047_ = lean_box(v___x_1046_);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget___boxed(lean_object* v_e_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(v_e_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_e_1049_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(lean_object* v_b_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_snd_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1141_; 
v_snd_1076_ = lean_ctor_get(v_b_1064_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_b_1064_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v_b_1064_, 0);
lean_dec(v_unused_1142_);
v___x_1078_ = v_b_1064_;
v_isShared_1079_ = v_isSharedCheck_1141_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_snd_1076_);
lean_dec(v_b_1064_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1141_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v_fst_1080_; lean_object* v_snd_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1140_; 
v_fst_1080_ = lean_ctor_get(v_snd_1076_, 0);
v_snd_1081_ = lean_ctor_get(v_snd_1076_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_snd_1076_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1083_ = v_snd_1076_;
v_isShared_1084_ = v_isSharedCheck_1140_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_snd_1081_);
lean_inc(v_fst_1080_);
lean_dec(v_snd_1076_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1140_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1085_ = lean_box(0);
v___x_1105_ = lean_array_get_size(v_snd_1081_);
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1107_ = lean_nat_dec_eq(v___x_1105_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_fst_1080_, v___y_1065_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref(v___x_1108_);
if (lean_obj_tag(v_a_1109_) == 1)
{
lean_object* v_val_1110_; uint8_t v_hasLambdas_1111_; 
v_val_1110_ = lean_ctor_get(v_a_1109_, 0);
lean_inc(v_val_1110_);
lean_dec_ref(v_a_1109_);
v_hasLambdas_1111_ = lean_ctor_get_uint8(v_val_1110_, sizeof(void*)*11 + 3);
if (v_hasLambdas_1111_ == 0)
{
lean_dec(v_val_1110_);
goto v___jp_1086_;
}
else
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_Meta_Grind_getEqcLambdas(v_val_1110_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v_val_1110_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref(v___x_1112_);
lean_inc(v_snd_1081_);
v___x_1114_ = l_Array_reverse___redArg(v_snd_1081_);
lean_inc(v_fst_1080_);
v___x_1115_ = l_Lean_Meta_Grind_propagateBetaEqs(v_a_1113_, v_fst_1080_, v___x_1114_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v_a_1113_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_dec_ref(v___x_1115_);
goto v___jp_1086_;
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_del_object(v___x_1083_);
lean_dec(v_snd_1081_);
lean_dec(v_fst_1080_);
lean_del_object(v___x_1078_);
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_del_object(v___x_1083_);
lean_dec(v_snd_1081_);
lean_dec(v_fst_1080_);
lean_del_object(v___x_1078_);
v_a_1124_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1112_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1112_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
else
{
lean_dec(v_a_1109_);
goto v___jp_1086_;
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_del_object(v___x_1083_);
lean_dec(v_snd_1081_);
lean_dec(v_fst_1080_);
lean_del_object(v___x_1078_);
v_a_1132_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1108_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1108_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
goto v___jp_1086_;
}
v___jp_1086_:
{
if (lean_obj_tag(v_fst_1080_) == 5)
{
lean_object* v_fn_1087_; lean_object* v_arg_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v_fn_1087_ = lean_ctor_get(v_fst_1080_, 0);
lean_inc_ref(v_fn_1087_);
v_arg_1088_ = lean_ctor_get(v_fst_1080_, 1);
lean_inc_ref(v_arg_1088_);
lean_dec_ref(v_fst_1080_);
v___x_1089_ = lean_array_push(v_snd_1081_, v_arg_1088_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v___x_1089_);
lean_ctor_set(v___x_1083_, 0, v_fn_1087_);
v___x_1091_ = v___x_1083_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_fn_1087_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 1, v___x_1091_);
lean_ctor_set(v___x_1078_, 0, v___x_1085_);
v___x_1093_ = v___x_1078_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
v_b_1064_ = v___x_1093_;
goto _start;
}
}
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___closed__0));
if (v_isShared_1084_ == 0)
{
v___x_1099_ = v___x_1083_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_fst_1080_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_snd_1081_);
v___x_1099_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1101_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 1, v___x_1099_);
lean_ctor_set(v___x_1078_, 0, v___x_1097_);
v___x_1101_ = v___x_1078_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___boxed(lean_object* v_b_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(v_b_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec(v___y_1144_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp(lean_object* v_e_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(v_e_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1205_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1205_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1205_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_unbox(v_a_1169_);
lean_dec(v_a_1169_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
lean_dec_ref(v_e_1156_);
v___x_1174_ = lean_box(0);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1174_);
v___x_1176_ = v___x_1171_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_del_object(v___x_1171_);
v___x_1178_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v_e_1156_);
lean_ctor_set(v___x_1180_, 1, v___x_1178_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(v___x_1181_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1196_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1196_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1196_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_fst_1187_; 
v_fst_1187_ = lean_ctor_get(v_a_1183_, 0);
lean_inc(v_fst_1187_);
lean_dec(v_a_1183_);
if (lean_obj_tag(v_fst_1187_) == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = lean_box(0);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1188_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
else
{
lean_object* v_val_1192_; lean_object* v___x_1194_; 
v_val_1192_ = lean_ctor_get(v_fst_1187_, 0);
lean_inc(v_val_1192_);
lean_dec_ref(v_fst_1187_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v_val_1192_);
v___x_1194_ = v___x_1185_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_val_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_a_1197_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1182_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1182_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec_ref(v_e_1156_);
v_a_1206_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1168_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1168_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp___boxed(lean_object* v_e_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_Meta_Grind_propagateBetaForNewApp(v_e_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec(v_a_1215_);
return v_res_1226_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Beta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Beta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Beta(builtin);
}
#ifdef __cplusplus
}
#endif
